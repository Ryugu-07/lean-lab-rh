import LeanLab.Riemann.DeBruijnNewmanThreshold
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option linter.style.header false

/-!
# Forward real-zero preservation for the de Bruijn-Newman family

This file develops the order-one and universal-factor infrastructure needed for the exact
forward preservation theorem.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

private theorem rpow_div_le_factorial_add_one_mul_exp
    {p u : ℝ} (hp : 1 < p) (hu : 0 ≤ u) :
    u ^ p / p ≤ (((Nat.ceil p).factorial : ℝ) + 1) * Real.exp (2 * u) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hdiv : u ^ p / p ≤ u ^ p := div_le_self (Real.rpow_nonneg hu p) hp.le
  by_cases hu1 : u ≤ 1
  · have hrpow : u ^ p ≤ 1 := Real.rpow_le_one hu hu1 hp0.le
    calc
      u ^ p / p ≤ u ^ p := hdiv
      _ ≤ 1 := hrpow
      _ ≤ (((Nat.ceil p).factorial : ℝ) + 1) * Real.exp (2 * u) := by
        have hexp : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hexp
          (show 0 ≤ ((Nat.ceil p).factorial : ℝ) + 1 by positivity)]
  · have h1u : 1 ≤ u := le_of_not_ge hu1
    have hpceil : p ≤ (Nat.ceil p : ℝ) := Nat.le_ceil p
    have hrpow : u ^ p ≤ u ^ (Nat.ceil p) := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le h1u hpceil
    have hbase : u ^ (Nat.ceil p) ≤ (2 * u) ^ (Nat.ceil p) := by
      gcongr
      linarith
    have hseries := Real.pow_div_factorial_le_exp (2 * u)
      (show 0 ≤ 2 * u by positivity) (Nat.ceil p)
    have hfactorial : 0 < ((Nat.ceil p).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hfactorial] at hseries
    calc
      u ^ p / p ≤ u ^ p := hdiv
      _ ≤ u ^ (Nat.ceil p) := hrpow
      _ ≤ (2 * u) ^ (Nat.ceil p) := hbase
      _ ≤ ((Nat.ceil p).factorial : ℝ) * Real.exp (2 * u) := by
        simpa only [mul_comm] using hseries
      _ ≤ (((Nat.ceil p).factorial : ℝ) + 1) * Real.exp (2 * u) := by
        gcongr
        linarith

private theorem exists_rpow_div_le_doubleExp
    {p : ℝ} (hp : 1 < p) :
    ∃ K ≥ 0, ∀ {u : ℝ}, 0 ≤ u →
      u ^ p / p ≤ (π / 4) * Real.exp (4 * u) + K := by
  let C : ℝ := ((Nat.ceil p).factorial : ℝ) + 1
  let K : ℝ := C ^ 2 / π
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro u hu
  have hpoly : u ^ p / p ≤ C * Real.exp (2 * u) := by
    simpa only [C] using rpow_div_le_factorial_add_one_mul_exp hp hu
  have hexp_sq : Real.exp (2 * u) ^ 2 = Real.exp (4 * u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have habsorb : C * Real.exp (2 * u) ≤
      (π / 4) * Real.exp (2 * u) ^ 2 + K := by
    have hsquare : 0 ≤ (π * Real.exp (2 * u) - 2 * C) ^ 2 := sq_nonneg _
    dsimp only [K]
    rw [show (π / 4) * Real.exp (2 * u) ^ 2 + C ^ 2 / π =
        (π ^ 2 * Real.exp (2 * u) ^ 2 / 4 + C ^ 2) / π by
      field_simp [ne_of_gt Real.pi_pos]]
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith
  calc
    u ^ p / p ≤ C * Real.exp (2 * u) := hpoly
    _ ≤ (π / 4) * Real.exp (2 * u) ^ 2 + K := habsorb
    _ = (π / 4) * Real.exp (4 * u) + K := by rw [hexp_sq]

private theorem integrableOn_exp_rpow_div_add_sq_mul_norm_deBruijnNewmanPhi
    (p : ℝ) (hp : 1 < p) (c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn
      (fun u : ℝ ↦ Real.exp (u ^ p / p + c * u ^ 2) *
        ‖deBruijnNewmanPhi u‖) (Ioi 0) := by
  obtain ⟨A, hA, hphi⟩ := exists_norm_deBruijnNewmanPhi_le_doubleExp
  obtain ⟨K, hK, hrpow⟩ := exists_rpow_div_le_doubleExp hp
  let major : ℝ → ℝ := fun u ↦
    A * Real.exp K *
      (Real.exp (c * u ^ 2 + 9 * u) *
        Real.exp (-(π / 4) * Real.exp (4 * u)))
  have hmajor : Integrable major (volume.restrict (Ioi 0)) := by
    exact ((integrableOn_dbn_exp_sq_mul_exp_neg_exp
      (π / 4) (by positivity) c hc 9).const_mul (A * Real.exp K))
  apply Integrable.mono' hmajor
  · have hterms : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : ℝ ↦ deBruijnNewmanPhiTerm n u)
        (volume.restrict (Ioi 0)) := fun n ↦ by
      apply Continuous.aestronglyMeasurable
      simp_rw [deBruijnNewmanPhiTerm_eq]
      fun_prop
    have hphi_meas : AEStronglyMeasurable deBruijnNewmanPhi
        (volume.restrict (Ioi 0)) := AEStronglyMeasurable.tsum hterms
    have hrpow_cont : Continuous (fun u : ℝ ↦ u ^ p) :=
      Real.continuous_rpow_const (zero_lt_one.trans hp).le
    have hscalar : Continuous
        (fun u : ℝ ↦ Real.exp (u ^ p / p + c * u ^ 2)) := by
      fun_prop
    exact hscalar.aestronglyMeasurable.mul hphi_meas.norm
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hphi_u := hphi hu0
    have hrpow_u := hrpow hu0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp (u ^ p / p + c * u ^ 2) * ‖deBruijnNewmanPhi u‖)]
    dsimp only [major]
    calc
      Real.exp (u ^ p / p + c * u ^ 2) * ‖deBruijnNewmanPhi u‖ ≤
          Real.exp (u ^ p / p + c * u ^ 2) *
            (A * Real.exp (9 * u) *
              Real.exp (-(π / 2) * Real.exp (4 * u))) := by gcongr
      _ ≤ A * Real.exp K *
          (Real.exp (c * u ^ 2 + 9 * u) *
            Real.exp (-(π / 4) * Real.exp (4 * u))) := by
        have hleft :
            Real.exp (u ^ p / p + c * u ^ 2) *
                (A * Real.exp (9 * u) *
                  Real.exp (-(π / 2) * Real.exp (4 * u))) =
              A * Real.exp
                (u ^ p / p + c * u ^ 2 +
                  (9 * u + -(π / 2) * Real.exp (4 * u))) := by
          simp only [Real.exp_add]
          ring
        have hright :
            A * Real.exp K *
                (Real.exp (c * u ^ 2 + 9 * u) *
                  Real.exp (-(π / 4) * Real.exp (4 * u))) =
              A * Real.exp
                (K + (c * u ^ 2 + 9 * u +
                  -(π / 4) * Real.exp (4 * u))) := by
          simp only [Real.exp_add]
          ring
        rw [hleft, hright]
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
        nlinarith [hrpow_u]

/-- Every spatial member of the source heat family has entire-function order at most one. -/
theorem deBruijnNewmanH_entireOfOrderAtMost_one (t : ℝ) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) (deBruijnNewmanH t) := by
  refine ⟨differentiable_deBruijnNewmanH t, ?_⟩
  intro ε hε
  let q : ℝ := 1 + ε
  let p : ℝ := Real.conjExponent q
  have hq : 1 < q := by dsimp [q]; linarith
  have hqp : q.HolderConjugate p := Real.HolderConjugate.conjExponent hq
  have hpq : p.HolderConjugate q := hqp.symm
  have hp : 1 < p := hpq.lt
  let g : ℝ → ℝ := fun u ↦
    Real.exp (u ^ p / p + |t| * u ^ 2) * ‖deBruijnNewmanPhi u‖
  have hg : Integrable g (volume.restrict (Ioi 0)) := by
    exact integrableOn_exp_rpow_div_add_sq_mul_norm_deBruijnNewmanPhi
      p hp |t| (abs_nonneg t)
  let J : ℝ := ∫ u, g u ∂volume.restrict (Ioi 0)
  have hJ : 0 ≤ J := by
    dsimp only [J]
    apply integral_nonneg_of_ae
    filter_upwards with u
    exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  let C : ℝ := J + 1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro z
  let F : ℝ → ℂ := fun u ↦
    (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (z * (u : ℂ)))
  have hF : Integrable F (volume.restrict (Ioi 0)) := by
    exact integrableOn_dbnHeatCosIntegrand t z
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ‖F u‖ ≤ Real.exp (‖z‖ ^ q / q) * g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hyoung : u * ‖z‖ ≤ u ^ p / p + ‖z‖ ^ q / q :=
      Real.young_inequality_of_nonneg hu0 (norm_nonneg z) hpq
    have htime : t * u ^ 2 ≤ |t| * u ^ 2 := by
      gcongr
      exact le_abs_self t
    dsimp only [F, g]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (z * (u : ℂ))‖ ≤
        Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (z * (u : ℂ))‖ := by
        gcongr
      _ ≤ Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖z‖ * u) := by
        gcongr
        exact norm_complex_cos_mul_real_le z hu0
      _ ≤ Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (u ^ p / p + ‖z‖ ^ q / q) := by
        gcongr
        nlinarith [hyoung]
      _ = Real.exp (‖z‖ ^ q / q) *
          (Real.exp (u ^ p / p + |t| * u ^ 2) *
            ‖deBruijnNewmanPhi u‖) := by
        simp only [Real.exp_add]
        ring
  have hmajor : Integrable
      (fun u ↦ Real.exp (‖z‖ ^ q / q) * g u)
      (volume.restrict (Ioi 0)) := hg.const_mul _
  have hnorm : ‖deBruijnNewmanH t z‖ ≤
      Real.exp (‖z‖ ^ q / q) * J := by
    rw [deBruijnNewmanH]
    change ‖∫ u, F u ∂volume.restrict (Ioi 0)‖ ≤ _
    calc
      ‖∫ u, F u ∂volume.restrict (Ioi 0)‖ ≤
          ∫ u, ‖F u‖ ∂volume.restrict (Ioi 0) :=
        norm_integral_le_integral_norm F
      _ ≤ ∫ u, Real.exp (‖z‖ ^ q / q) * g u
          ∂volume.restrict (Ioi 0) :=
        integral_mono_ae hF.norm hmajor hpoint
      _ = Real.exp (‖z‖ ^ q / q) * J := by
        rw [integral_const_mul]
  have hq0 : 0 ≤ q := zero_le_one.trans hq.le
  have hbase : 1 ≤ (1 + ‖z‖) ^ q := by
    exact Real.one_le_rpow (by linarith [norm_nonneg z]) hq0
  have hzpow : ‖z‖ ^ q ≤ (1 + ‖z‖) ^ q := by
    exact Real.rpow_le_rpow (norm_nonneg z) (by linarith) hq0
  have hzdiv : ‖z‖ ^ q / q ≤ ‖z‖ ^ q :=
    div_le_self (Real.rpow_nonneg (norm_nonneg z) q) hq.le
  have hexponent : ‖z‖ ^ q / q + J ≤ C * (1 + ‖z‖) ^ q := by
    dsimp only [C]
    have hJscale := mul_le_mul_of_nonneg_left hbase hJ
    nlinarith
  calc
    ‖deBruijnNewmanH t z‖ ≤ Real.exp (‖z‖ ^ q / q) * J := hnorm
    _ ≤ Real.exp (‖z‖ ^ q / q) * Real.exp J := by
      gcongr
      linarith [Real.add_one_le_exp J]
    _ = Real.exp (‖z‖ ^ q / q + J) := by rw [Real.exp_add]
    _ ≤ Real.exp (C * (1 + ‖z‖) ^ q) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp (C * (1 + ‖z‖) ^ ((1 : ℝ) + ε)) := by rfl

@[simp]
theorem deBruijnNewmanH_neg (t : ℝ) (z : ℂ) :
    deBruijnNewmanH t (-z) = deBruijnNewmanH t z := by
  rw [deBruijnNewmanH]
  congr 1
  funext u
  simp

theorem summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq (t : ℝ) :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀
          (deBruijnNewmanH t) (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
  have hnot : ∃ z : ℂ, deBruijnNewmanH t z ≠ 0 :=
    ⟨0, deBruijnNewmanH_zero_ne_zero t⟩
  simpa using
    (deBruijnNewmanH_entireOfOrderAtMost_one t).summable_norm_inv_pow_divisorZeroIndex₀
      (show (0 : ℝ) ≤ 1 by norm_num) hnot

theorem exists_deBruijnNewmanH_hadamard_factorization (t : ℝ) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
      deBruijnNewmanH t z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
          (Set.univ : Set ℂ) z := by
  have hnot : ∃ z : ℂ, deBruijnNewmanH t z ≠ 0 :=
    ⟨0, deBruijnNewmanH_zero_ne_zero t⟩
  obtain ⟨P, hdegree, hfactor⟩ :=
    Complex.Hadamard.hadamard_factorization_of_order
      (show (0 : ℝ) ≤ 1 by norm_num) hnot
      (deBruijnNewmanH_entireOfOrderAtMost_one t)
  have horder0 : analyticOrderNatAt (deBruijnNewmanH t) 0 = 0 := by
    by_contra horder
    exact deBruijnNewmanH_zero_ne_zero t
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero horder)
  refine ⟨P, ?_, ?_⟩
  · simpa using hdegree
  · intro z
    simpa [horder0] using hfactor z

theorem deBruijnNewmanH_divisorZeroIndex_im_eq_zero
    {t : ℝ} (ht : deBruijnNewmanAllZerosReal t)
    (p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ)) :
    (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 := by
  apply ht
  have hsupport :=
    Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support
      (f := deBruijnNewmanH t) (U := (Set.univ : Set ℂ)) p
  have hdivisor : MeromorphicOn.divisor (deBruijnNewmanH t) Set.univ
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    simpa only [Function.mem_support] using hsupport
  have horder : analyticOrderNatAt (deBruijnNewmanH t)
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    intro hzero
    apply hdivisor
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_deBruijnNewmanH t)]
    simp [hzero]
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero horder

private theorem logDeriv_deBruijnNewmanH_eq_polynomial_derivative_add_tsum
    {t : ℝ} {P : Polynomial ℂ} {z : ℂ}
    (hfactor : ∀ w : ℂ, deBruijnNewmanH t w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
          (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv (deBruijnNewmanH t) z =
      Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀
            (deBruijnNewmanH t) (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let G : ℂ → ℂ :=
    Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
      (Set.univ : Set ℂ)
  have hfun : deBruijnNewmanH t = fun w : ℂ ↦
      Complex.exp (Polynomial.eval w P) * G w := by
    funext w
    simpa only [G] using hfactor w
  have hdiff_exp : DifferentiableAt ℂ
      (fun w : ℂ ↦ Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z
      (P.hasDerivAt z)).differentiableAt
  have hsum := summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t
  have hprod_ne :
      Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
        (Set.univ : Set ℂ) z ≠ 0 :=
    Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne
      1 (deBruijnNewmanH t) hsum hz
  calc
    logDeriv (deBruijnNewmanH t) z =
        logDeriv (fun w : ℂ ↦ Complex.exp (Polynomial.eval w P) * G w) z := by
      rw [hfun]
    _ = logDeriv (fun w : ℂ ↦ Complex.exp (Polynomial.eval w P)) z +
        logDeriv G z := by
      exact logDeriv_mul z (Complex.exp_ne_zero _) (by simpa only [G] using hprod_ne)
        hdiff_exp
        (by
          simpa only [G] using
            Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ
              1 (deBruijnNewmanH t) hsum z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀
            (deBruijnNewmanH t) (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
      rw [Polynomial.logDeriv_exp_eval]
      rw [show logDeriv G z =
          ∑' p : Complex.Hadamard.divisorZeroIndex₀
              (deBruijnNewmanH t) (Set.univ : Set ℂ),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) from by
        simpa only [G] using
          Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
            hsum hz]

theorem exists_deBruijnNewmanH_constant_hadamard_factorization (t : ℝ) :
    ∃ b : ℂ, ∀ z : ℂ,
      deBruijnNewmanH t z = Complex.exp b *
        Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
          (Set.univ : Set ℂ) z := by
  obtain ⟨P, hdegree, hfactor⟩ := exists_deBruijnNewmanH_hadamard_factorization t
  have hz0 : ∀ p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ),
      (0 : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p
    exact (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm
  have hlog :=
    logDeriv_deBruijnNewmanH_eq_polynomial_derivative_add_tsum hfactor hz0
  have hsum :
      (∑' p : Complex.Hadamard.divisorZeroIndex₀
          (deBruijnNewmanH t) (Set.univ : Set ℂ),
        (1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p)) = 0 := by
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero]
  have hlogzero : logDeriv (deBruijnNewmanH t) 0 = 0 := by
    rw [logDeriv_apply, deriv_deBruijnNewmanH_zero]
    simp
  have heval : Polynomial.eval 0 P.derivative = 0 := by
    rw [hlogzero, hsum] at hlog
    simpa using hlog.symm
  have hlinear := Polynomial.eq_X_add_C_of_degree_le_one hdegree
  have hcoeff : P.coeff 1 = 0 := by
    rw [hlinear] at heval
    simpa using heval
  have hconstant : P = Polynomial.C (P.coeff 0) := by
    rw [hlinear, hcoeff]
    simp
  rw [hconstant] at hfactor
  refine ⟨P.coeff 0, ?_⟩
  intro z
  simpa only [Polynomial.eval_C] using hfactor z

private theorem norm_weierstrassFactor_one_sub_I_lt_add_I
    {r z : ℂ} {a : ℝ} (hr0 : r ≠ 0) (hrim : r.im = 0)
    (ha : 0 < a) (hz : 0 < z.im) :
    ‖Complex.weierstrassFactor 1 ((z - I * (a : ℂ)) / r)‖ <
      ‖Complex.weierstrassFactor 1 ((z + I * (a : ℂ)) / r)‖ := by
  have hrnorm : 0 < Complex.normSq r := Complex.normSq_pos.mpr hr0
  have hsq : Complex.normSq (1 - (z - I * (a : ℂ)) / r) <
      Complex.normSq (1 - (z + I * (a : ℂ)) / r) := by
    rw [show 1 - (z - I * (a : ℂ)) / r =
        (r - (z - I * (a : ℂ))) / r by field_simp]
    rw [show 1 - (z + I * (a : ℂ)) / r =
        (r - (z + I * (a : ℂ))) / r by field_simp]
    rw [Complex.normSq_div, Complex.normSq_div]
    apply div_lt_div_of_pos_right _ hrnorm
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub,
      hrim]
    nlinarith
  have hnorm : ‖1 - (z - I * (a : ℂ)) / r‖ <
      ‖1 - (z + I * (a : ℂ)) / r‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (1 - (z - I * (a : ℂ)) / r),
      norm_nonneg (1 - (z + I * (a : ℂ)) / r)]
  have hexp :
      ‖Complex.exp (Complex.partialLogSum 1 ((z - I * (a : ℂ)) / r))‖ =
        ‖Complex.exp (Complex.partialLogSum 1 ((z + I * (a : ℂ)) / r))‖ := by
    simp only [Complex.partialLogSum_eq_sum, Finset.range_one, Finset.sum_singleton,
      zero_add, pow_one, Complex.norm_exp]
    simp [Complex.div_re, hrim]
  rw [Complex.weierstrassFactor_def, Complex.weierstrassFactor_def,
    norm_mul, norm_mul, hexp]
  exact mul_lt_mul_of_pos_right hnorm (norm_pos_iff.mpr (Complex.exp_ne_zero _))

private theorem norm_tprod_lt_norm_tprod_of_pointwise
    {ι : Type*} {f g : ι → ℂ} (hf : Multipliable f) (hg : Multipliable g)
    (hle : ∀ i, ‖f i‖ ≤ ‖g i‖) {i₀ : ι} (hlt : ‖f i₀‖ < ‖g i₀‖)
    (hg0 : ∏' i, g i ≠ 0) :
    ‖∏' i, f i‖ < ‖∏' i, g i‖ := by
  classical
  let c : ℝ := ‖f i₀‖ / ‖g i₀‖
  have hgi : 0 < ‖g i₀‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hc0 : 0 ≤ c := div_nonneg (norm_nonneg _) hgi.le
  have hc1 : c < 1 := (div_lt_one hgi).2 hlt
  have hbound : (∏' i, ‖f i‖) ≤ c * ∏' i, ‖g i‖ := by
    apply le_of_tendsto_of_tendsto hf.norm.hasProd
      (Filter.Tendsto.const_mul c hg.norm.hasProd)
    filter_upwards [Filter.eventually_atTop.2
      ⟨{i₀}, fun s hs ↦ hs (Finset.mem_singleton_self i₀)⟩] with s hs
    have htail : (∏ i ∈ s.erase i₀, ‖f i‖) ≤ ∏ i ∈ s.erase i₀, ‖g i‖ :=
      Finset.prod_le_prod (fun i _ ↦ norm_nonneg (f i)) (fun i _ ↦ hle i)
    calc
      (∏ i ∈ s, ‖f i‖) = ‖f i₀‖ * ∏ i ∈ s.erase i₀, ‖f i‖ := by
        rw [← Finset.prod_erase_mul _ _ hs]
        ac_rfl
      _ ≤ ‖f i₀‖ * ∏ i ∈ s.erase i₀, ‖g i‖ :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg _)
      _ = c * (‖g i₀‖ * ∏ i ∈ s.erase i₀, ‖g i‖) := by
        rw [show ‖f i₀‖ = c * ‖g i₀‖ by
          dsimp only [c]
          exact (div_mul_cancel₀ _ hgi.ne').symm]
        ring
      _ = c * ∏ i ∈ s, ‖g i‖ := by
        rw [← Finset.prod_erase_mul _ _ hs]
        congr 1
        ac_rfl
  have hgpos : 0 < ∏' i, ‖g i‖ := by
    rw [← hg.norm_tprod]
    exact norm_pos_iff.mpr hg0
  calc
    ‖∏' i, f i‖ = ∏' i, ‖f i‖ := hf.norm_tprod
    _ ≤ c * ∏' i, ‖g i‖ := hbound
    _ < ∏' i, ‖g i‖ := by nlinarith
    _ = ‖∏' i, g i‖ := hg.norm_tprod.symm

private theorem norm_deBruijnNewmanH_canonicalProduct_sub_I_lt_add_I
    {t : ℝ} (ht : deBruijnNewmanAllZerosReal t)
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im)
    (p0 : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ)) :
    ‖Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
        (Set.univ : Set ℂ) (z - I * (a : ℂ))‖ <
      ‖Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
        (Set.univ : Set ℂ) (z + I * (a : ℂ))‖ := by
  let zm : ℂ := z - I * (a : ℂ)
  let zp : ℂ := z + I * (a : ℂ)
  let fm : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ) → ℂ := fun p ↦
    Complex.weierstrassFactor 1
      (zm / Complex.Hadamard.divisorZeroIndex₀_val p)
  let fp : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ) → ℂ := fun p ↦
    Complex.weierstrassFactor 1
      (zp / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hsum := summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t
  have hm : Multipliable fm := by
    have hprod :=
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        1 (deBruijnNewmanH t) hsum).hasProd (Set.mem_univ zm)
    simpa only [fm, zm] using hprod.multipliable
  have hp : Multipliable fp := by
    have hprod :=
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        1 (deBruijnNewmanH t) hsum).hasProd (Set.mem_univ zp)
    simpa only [fp, zp] using hprod.multipliable
  have hstrict : ∀ p, ‖fm p‖ < ‖fp p‖ := by
    intro p
    exact norm_weierstrassFactor_one_sub_I_lt_add_I
      (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
      (deBruijnNewmanH_divisorZeroIndex_im_eq_zero ht p) ha hz
  have hproduct_ne : ∏' p, fp p ≠ 0 := by
    obtain ⟨b, hfactor⟩ := exists_deBruijnNewmanH_constant_hadamard_factorization t
    have hHzp : deBruijnNewmanH t zp ≠ 0 := by
      intro hzero
      have hreal := ht zp hzero
      have hzp_im : 0 < zp.im := by
        simp only [zp, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
        linarith
      linarith
    intro hzero
    apply hHzp
    rw [hfactor zp]
    change Complex.exp b * (∏' p, fp p) = 0
    rw [hzero, mul_zero]
  change ‖∏' p, fm p‖ < ‖∏' p, fp p‖
  exact norm_tprod_lt_norm_tprod_of_pointwise hm hp
    (fun p ↦ (hstrict p).le) (hstrict p0) hproduct_ne

private theorem deBruijnNewman_verticalAverage_ne_zero_of_im_pos
    {t : ℝ} (ht : deBruijnNewmanAllZerosReal t)
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    (deBruijnNewmanH t (z + I * (a : ℂ)) +
      deBruijnNewmanH t (z - I * (a : ℂ))) / 2 ≠ 0 := by
  intro havg
  have hsum : deBruijnNewmanH t (z + I * (a : ℂ)) +
      deBruijnNewmanH t (z - I * (a : ℂ)) = 0 := by
    simpa using havg
  obtain ⟨b, hfactor⟩ := exists_deBruijnNewmanH_constant_hadamard_factorization t
  let Z := Complex.Hadamard.divisorZeroIndex₀
    (deBruijnNewmanH t) (Set.univ : Set ℂ)
  cases isEmpty_or_nonempty Z with
  | inl _ =>
      have hproduct : ∀ w : ℂ,
          Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanH t)
            (Set.univ : Set ℂ) w = 1 := by
        intro w
        simp only [Complex.Hadamard.divisorCanonicalProduct]
        exact tprod_empty
      have hexpzero : Complex.exp b = 0 := by
        have := hsum
        rw [hfactor, hfactor, hproduct, hproduct] at this
        have htwo : (2 : ℂ) * Complex.exp b = 0 := by
          simpa only [mul_one, two_mul] using this
        exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact Complex.exp_ne_zero b hexpzero
  | inr _ =>
      let p0 : Z := Classical.choice (inferInstance : Nonempty Z)
      have hproduct := norm_deBruijnNewmanH_canonicalProduct_sub_I_lt_add_I
        ht ha hz p0
      have hstrict :
          ‖deBruijnNewmanH t (z - I * (a : ℂ))‖ <
            ‖deBruijnNewmanH t (z + I * (a : ℂ))‖ := by
        rw [hfactor, hfactor, norm_mul, norm_mul]
        exact mul_lt_mul_of_pos_left hproduct
          (norm_pos_iff.mpr (Complex.exp_ne_zero b))
      have heq : deBruijnNewmanH t (z + I * (a : ℂ)) =
          -deBruijnNewmanH t (z - I * (a : ℂ)) := by
        exact eq_neg_of_add_eq_zero_left hsum
      have hnorm : ‖deBruijnNewmanH t (z - I * (a : ℂ))‖ =
          ‖deBruijnNewmanH t (z + I * (a : ℂ))‖ := by
        rw [heq, norm_neg]
      exact hstrict.ne hnorm

private theorem deBruijnNewman_verticalAverage_neg
    (t a : ℝ) (z : ℂ) :
    (deBruijnNewmanH t (-z + I * (a : ℂ)) +
      deBruijnNewmanH t (-z - I * (a : ℂ))) / 2 =
    (deBruijnNewmanH t (z + I * (a : ℂ)) +
      deBruijnNewmanH t (z - I * (a : ℂ))) / 2 := by
  rw [show -z + I * (a : ℂ) = -(z - I * (a : ℂ)) by ring,
    show -z - I * (a : ℂ) = -(z + I * (a : ℂ)) by ring,
    deBruijnNewmanH_neg, deBruijnNewmanH_neg, add_comm]

theorem deBruijnNewman_verticalAverage_allZerosReal
    {t : ℝ} (ht : deBruijnNewmanAllZerosReal t)
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ z : ℂ,
      (deBruijnNewmanH t (z + I * (a : ℂ)) +
        deBruijnNewmanH t (z - I * (a : ℂ))) / 2 = 0 →
      z.im = 0 := by
  intro z havg
  rcases ha.eq_or_lt with rfl | ha
  · apply ht z
    simpa using havg
  · rcases lt_trichotomy z.im 0 with hz | hz | hz
    · exfalso
      apply deBruijnNewman_verticalAverage_ne_zero_of_im_pos ht ha
        (show 0 < (-z).im by simpa using neg_pos.mpr hz)
      rw [deBruijnNewman_verticalAverage_neg]
      exact havg
    · exact hz
    · exact (deBruijnNewman_verticalAverage_ne_zero_of_im_pos ht ha hz havg).elim

private theorem deriv_zero_of_even
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (heven : ∀ z, F (-z) = F z) :
    deriv F 0 = 0 := by
  have hfun : (fun z : ℂ ↦ F (-z)) = F := funext heven
  have hderiv := congrArg (fun G : ℂ → ℂ ↦ deriv G 0) hfun
  have hleft : deriv (fun z : ℂ ↦ F (-z)) 0 = -deriv F 0 := by
    have houter : HasDerivAt F (deriv F 0) (0 : ℂ) := (hF 0).hasDerivAt
    have hinner : HasDerivAt (fun z : ℂ ↦ -z) (-1) (0 : ℂ) :=
      hasDerivAt_neg' (0 : ℂ)
    have hcomp : HasDerivAt (F ∘ fun z : ℂ ↦ -z)
        (deriv F 0 * (-1)) (0 : ℂ) :=
      HasDerivAt.comp_of_eq (x := (0 : ℂ)) (y := (0 : ℂ)) houter hinner (by simp)
    simpa [Function.comp_def] using hcomp.deriv
  rw [hleft] at hderiv
  exact CharZero.neg_eq_self_iff.mp hderiv

private theorem logDeriv_eq_polynomial_derivative_add_tsum
    {F : ℂ → ℂ} {P : Polynomial ℂ} {z : ℂ}
    (hsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hfactor : ∀ w : ℂ, F w = Complex.exp (Polynomial.eval w P) *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv F z = Polynomial.eval z P.derivative +
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let G : ℂ → ℂ := Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ)
  have hfun : F = fun w : ℂ ↦ Complex.exp (Polynomial.eval w P) * G w := by
    funext w
    simpa only [G] using hfactor w
  have hdiff_exp : DifferentiableAt ℂ
      (fun w : ℂ ↦ Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z
      (P.hasDerivAt z)).differentiableAt
  have hprod_ne : Complex.Hadamard.divisorCanonicalProduct 1 F
      (Set.univ : Set ℂ) z ≠ 0 :=
    Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne 1 F hsum hz
  calc
    logDeriv F z = logDeriv
        (fun w : ℂ ↦ Complex.exp (Polynomial.eval w P) * G w) z := by rw [hfun]
    _ = logDeriv (fun w : ℂ ↦ Complex.exp (Polynomial.eval w P)) z +
        logDeriv G z := by
      exact logDeriv_mul z (Complex.exp_ne_zero _) (by simpa only [G] using hprod_ne)
        hdiff_exp
        (by
          simpa only [G] using
            Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ 1 F hsum z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
      rw [Polynomial.logDeriv_exp_eval]
      rw [show logDeriv G z =
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) from by
        simpa only [G] using
          Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
            hsum hz]

private theorem exists_constant_hadamard_factorization
    {F : ℂ → ℂ} (horder : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) F)
    (hzero : F 0 ≠ 0) (hderiv : deriv F 0 = 0) :
    ∃ b : ℂ, ∀ z : ℂ, F z = Complex.exp b *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ) z := by
  have hnot : ∃ z : ℂ, F z ≠ 0 := ⟨0, hzero⟩
  have hsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
    simpa using horder.summable_norm_inv_pow_divisorZeroIndex₀
      (show (0 : ℝ) ≤ 1 by norm_num) hnot
  obtain ⟨P, hdegree, hfactor0⟩ :=
    Complex.Hadamard.hadamard_factorization_of_order
      (show (0 : ℝ) ≤ 1 by norm_num) hnot horder
  have horder0 : analyticOrderNatAt F 0 = 0 := by
    by_contra horder0
    exact hzero (apply_eq_zero_of_analyticOrderNatAt_ne_zero horder0)
  have hfactor : ∀ z : ℂ, F z = Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ) z := by
    intro z
    simpa [horder0] using hfactor0 z
  have hz0 : ∀ p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
      (0 : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p
    exact (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm
  have hlog := logDeriv_eq_polynomial_derivative_add_tsum hsum hfactor hz0
  have hseries :
      (∑' p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
        (1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p)) = 0 := by
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero]
  have hlogzero : logDeriv F 0 = 0 := by
    rw [logDeriv_apply, hderiv]
    simp
  have heval : Polynomial.eval 0 P.derivative = 0 := by
    rw [hlogzero, hseries] at hlog
    simpa using hlog.symm
  have hdegree' : P.degree ≤ 1 := by simpa using hdegree
  have hlinear := Polynomial.eq_X_add_C_of_degree_le_one hdegree'
  have hcoeff : P.coeff 1 = 0 := by
    rw [hlinear] at heval
    simpa using heval
  have hconstant : P = Polynomial.C (P.coeff 0) := by
    rw [hlinear, hcoeff]
    simp
  rw [hconstant] at hfactor
  refine ⟨P.coeff 0, ?_⟩
  intro z
  simpa only [Polynomial.eval_C] using hfactor z

private theorem divisorZeroIndex_im_eq_zero
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hreal : ∀ z : ℂ, F z = 0 → z.im = 0)
    (p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 := by
  apply hreal
  have hsupport :=
    Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support
      (f := F) (U := (Set.univ : Set ℂ)) p
  have hdivisor : MeromorphicOn.divisor F Set.univ
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    simpa only [Function.mem_support] using hsupport
  have horder : analyticOrderNatAt F
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    intro hzero
    apply hdivisor
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int hF]
    simp [hzero]
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero horder

private theorem norm_canonicalProduct_sub_I_lt_add_I
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hreal : ∀ w : ℂ, F w = 0 → w.im = 0)
    {b : ℂ} (hfactor : ∀ w : ℂ, F w = Complex.exp b *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ) w)
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im)
    (p0 : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    ‖Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ)
        (z - I * (a : ℂ))‖ <
      ‖Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ)
        (z + I * (a : ℂ))‖ := by
  let zm : ℂ := z - I * (a : ℂ)
  let zp : ℂ := z + I * (a : ℂ)
  let fm : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) → ℂ := fun p ↦
    Complex.weierstrassFactor 1
      (zm / Complex.Hadamard.divisorZeroIndex₀_val p)
  let fp : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) → ℂ := fun p ↦
    Complex.weierstrassFactor 1
      (zp / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hm : Multipliable fm := by
    have hprod :=
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        1 F hsum).hasProd (Set.mem_univ zm)
    simpa only [fm, zm] using hprod.multipliable
  have hp : Multipliable fp := by
    have hprod :=
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        1 F hsum).hasProd (Set.mem_univ zp)
    simpa only [fp, zp] using hprod.multipliable
  have hstrict : ∀ p, ‖fm p‖ < ‖fp p‖ := by
    intro p
    exact norm_weierstrassFactor_one_sub_I_lt_add_I
      (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
      (divisorZeroIndex_im_eq_zero hF hreal p) ha hz
  have hproduct_ne : ∏' p, fp p ≠ 0 := by
    have hFzp : F zp ≠ 0 := by
      intro hzero
      have hreal_zp := hreal zp hzero
      have hzp_im : 0 < zp.im := by
        simp only [zp, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
        linarith
      linarith
    intro hzero
    apply hFzp
    rw [hfactor zp]
    change Complex.exp b * (∏' p, fp p) = 0
    rw [hzero, mul_zero]
  change ‖∏' p, fm p‖ < ‖∏' p, fp p‖
  exact norm_tprod_lt_norm_tprod_of_pointwise hm hp
    (fun p ↦ (hstrict p).le) (hstrict p0) hproduct_ne

private theorem verticalAverage_allZerosReal
    {F : ℂ → ℂ} (horder : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) F)
    (heven : ∀ z : ℂ, F (-z) = F z) (hzero : F 0 ≠ 0)
    (hreal : ∀ z : ℂ, F z = 0 → z.im = 0)
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ z : ℂ, (F (z + I * (a : ℂ)) + F (z - I * (a : ℂ))) / 2 = 0 →
      z.im = 0 := by
  intro z havg
  rcases ha.eq_or_lt with rfl | ha
  · apply hreal z
    simpa using havg
  · have hderiv : deriv F 0 = 0 := deriv_zero_of_even horder.differentiable heven
    obtain ⟨b, hfactor⟩ := exists_constant_hadamard_factorization horder hzero hderiv
    have hsum : Summable
        (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
          ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
      simpa using horder.summable_norm_inv_pow_divisorZeroIndex₀
        (show (0 : ℝ) ≤ 1 by norm_num) ⟨0, hzero⟩
    have hupper : ∀ {w : ℂ}, 0 < w.im →
        (F (w + I * (a : ℂ)) + F (w - I * (a : ℂ))) / 2 ≠ 0 := by
      intro w hw havg_w
      have hsum_w : F (w + I * (a : ℂ)) + F (w - I * (a : ℂ)) = 0 := by
        simpa using havg_w
      let Z := Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)
      cases isEmpty_or_nonempty Z with
      | inl _ =>
          have hproduct : ∀ v : ℂ,
              Complex.Hadamard.divisorCanonicalProduct 1 F
                (Set.univ : Set ℂ) v = 1 := by
            intro v
            simp only [Complex.Hadamard.divisorCanonicalProduct]
            exact tprod_empty
          have hexpzero : Complex.exp b = 0 := by
            have h := hsum_w
            rw [hfactor, hfactor, hproduct, hproduct] at h
            have htwo : (2 : ℂ) * Complex.exp b = 0 := by
              simpa only [mul_one, two_mul] using h
            exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
          exact Complex.exp_ne_zero b hexpzero
      | inr _ =>
          let p0 : Z := Classical.choice (inferInstance : Nonempty Z)
          have hproduct := norm_canonicalProduct_sub_I_lt_add_I
            horder.differentiable hsum hreal hfactor ha hw p0
          have hstrict : ‖F (w - I * (a : ℂ))‖ < ‖F (w + I * (a : ℂ))‖ := by
            rw [hfactor, hfactor, norm_mul, norm_mul]
            exact mul_lt_mul_of_pos_left hproduct
              (norm_pos_iff.mpr (Complex.exp_ne_zero b))
          have heq : F (w + I * (a : ℂ)) = -F (w - I * (a : ℂ)) :=
            eq_neg_of_add_eq_zero_left hsum_w
          have hnorm : ‖F (w - I * (a : ℂ))‖ = ‖F (w + I * (a : ℂ))‖ := by
            rw [heq, norm_neg]
          exact hstrict.ne hnorm
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · exfalso
      apply hupper (show 0 < (-z).im by simpa using neg_pos.mpr hz)
      have hneg :
          (F (-z + I * (a : ℂ)) + F (-z - I * (a : ℂ))) / 2 =
            (F (z + I * (a : ℂ)) + F (z - I * (a : ℂ))) / 2 := by
        rw [show -z + I * (a : ℂ) = -(z - I * (a : ℂ)) by ring,
          show -z - I * (a : ℂ) = -(z + I * (a : ℂ)) by ring,
          heven, heven, add_comm]
      rw [hneg]
      exact havg
    · exact hz
    · exact (hupper hz havg).elim

private def verticalAverage (a : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z + I * (a : ℂ)) + F (z - I * (a : ℂ))) / 2

private theorem entireOfOrderAtMost_verticalAverage
    {F : ℂ → ℂ} (horder : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) F)
    (a : ℝ) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) (verticalAverage a F) := by
  let hp := horder.comp_add_const (show (0 : ℝ) ≤ 1 by norm_num) (I * (a : ℂ))
  let hm := horder.comp_sub_const (show (0 : ℝ) ≤ 1 by norm_num) (I * (a : ℂ))
  refine ⟨?_, ?_⟩
  · exact (hp.differentiable.add hm.differentiable).div_const 2
  · intro ε hε
    obtain ⟨Cp, hCp, hpbound⟩ := hp.exists_bound hε
    obtain ⟨Cm, hCm, hmbound⟩ := hm.exists_bound hε
    refine ⟨Cp + Cm, add_pos hCp hCm, ?_⟩
    intro z
    let R : ℝ := (1 + ‖z‖) ^ ((1 : ℝ) + ε)
    have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
    have hp' : ‖F (z + I * (a : ℂ))‖ ≤ Real.exp ((Cp + Cm) * R) := by
      calc
        ‖F (z + I * (a : ℂ))‖ ≤ Real.exp (Cp * R) := hpbound z
        _ ≤ Real.exp ((Cp + Cm) * R) := Real.exp_le_exp.mpr (by nlinarith)
    have hm' : ‖F (z - I * (a : ℂ))‖ ≤ Real.exp ((Cp + Cm) * R) := by
      calc
        ‖F (z - I * (a : ℂ))‖ ≤ Real.exp (Cm * R) := hmbound z
        _ ≤ Real.exp ((Cp + Cm) * R) := Real.exp_le_exp.mpr (by nlinarith)
    change ‖(F (z + I * (a : ℂ)) + F (z - I * (a : ℂ))) / 2‖ ≤
      Real.exp ((Cp + Cm) * R)
    calc
      ‖(F (z + I * (a : ℂ)) + F (z - I * (a : ℂ))) / 2‖ =
          ‖F (z + I * (a : ℂ)) + F (z - I * (a : ℂ))‖ / 2 := by
        rw [norm_div]
        norm_num
      _ ≤ (‖F (z + I * (a : ℂ))‖ + ‖F (z - I * (a : ℂ))‖) / 2 := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (Real.exp ((Cp + Cm) * R) + Real.exp ((Cp + Cm) * R)) / 2 := by
        gcongr
      _ = Real.exp ((Cp + Cm) * R) := by ring

private theorem verticalAverage_even
    {F : ℂ → ℂ} (heven : ∀ z : ℂ, F (-z) = F z) (a : ℝ) :
    ∀ z : ℂ, verticalAverage a F (-z) = verticalAverage a F z := by
  intro z
  rw [verticalAverage, verticalAverage,
    show -z + I * (a : ℂ) = -(z - I * (a : ℂ)) by ring,
    show -z - I * (a : ℂ) = -(z + I * (a : ℂ)) by ring,
    heven, heven, add_comm]

private theorem verticalAverage_zero_ne
    {F : ℂ → ℂ} (heven : ∀ z : ℂ, F (-z) = F z)
    (hreal : ∀ z : ℂ, F z = 0 → z.im = 0) (hzero : F 0 ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) : verticalAverage a F 0 ≠ 0 := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa [verticalAverage] using hzero
  · intro havg
    have harg : -(I * (a : ℂ)) = (0 : ℂ) - I * (a : ℂ) := by ring
    have heq : F (0 - I * (a : ℂ)) = F (I * (a : ℂ)) := by
      rw [← harg, heven]
    have hFia : F (I * (a : ℂ)) = 0 := by
      rw [verticalAverage, zero_add, heq] at havg
      calc
        F (I * (a : ℂ)) =
            (F (I * (a : ℂ)) + F (I * (a : ℂ))) / 2 := by ring
        _ = 0 := havg
    have him := hreal (I * (a : ℂ)) hFia
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul] at him
    linarith

private structure VerticalAverageAdmissible (F : ℂ → ℂ) : Prop where
  order_one : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) F
  even : ∀ z : ℂ, F (-z) = F z
  zero_ne : F 0 ≠ 0
  zeros_real : ∀ z : ℂ, F z = 0 → z.im = 0

private theorem VerticalAverageAdmissible.verticalAverage
    {F : ℂ → ℂ} (hF : VerticalAverageAdmissible F)
    {a : ℝ} (ha : 0 ≤ a) : VerticalAverageAdmissible (verticalAverage a F) := by
  refine ⟨entireOfOrderAtMost_verticalAverage hF.order_one a,
    verticalAverage_even hF.even a,
    verticalAverage_zero_ne hF.even hF.zeros_real hF.zero_ne ha, ?_⟩
  intro z hz
  exact verticalAverage_allZerosReal hF.order_one hF.even hF.zero_ne hF.zeros_real ha z hz

private def verticalAverageIterate (a : ℝ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, F => F
  | n + 1, F => verticalAverage a (verticalAverageIterate a n F)

private theorem VerticalAverageAdmissible.verticalAverageIterate
    {F : ℂ → ℂ} (hF : VerticalAverageAdmissible F)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    VerticalAverageAdmissible (verticalAverageIterate a n F) := by
  induction n with
  | zero => exact hF
  | succ n hn => exact hn.verticalAverage ha

private theorem cos_add_I_average (z : ℂ) (a u : ℝ) :
    (Complex.cos ((z + I * (a : ℂ)) * (u : ℂ)) +
      Complex.cos ((z - I * (a : ℂ)) * (u : ℂ))) / 2 =
    Complex.cos (z * (u : ℂ)) * (Real.cosh (a * u) : ℂ) := by
  rw [show (z + I * (a : ℂ)) * (u : ℂ) =
      z * (u : ℂ) + ((a * u : ℝ) : ℂ) * I by push_cast; ring,
    show (z - I * (a : ℂ)) * (u : ℂ) =
      z * (u : ℂ) - ((a * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cos_add, Complex.cos_sub, Complex.cos_mul_I, Complex.sin_mul_I]
  push_cast
  ring

private def dbnCoshIntegrand (t a : ℝ) (n : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
    Complex.cos (z * (u : ℂ))) * (Real.cosh (a * u) ^ n : ℝ)

private theorem integrableOn_dbn_cosh_pow_integrand
    (t a : ℝ) (n : ℕ) (z : ℂ) :
    IntegrableOn (dbnCoshIntegrand t a n z) (Ioi 0) := by
  change IntegrableOn
    (fun u : ℝ ↦
      (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ))) * (Real.cosh (a * u) ^ n : ℝ))
    (Ioi 0)
  let c : ℝ := |t| + (n : ℝ) * a ^ 2 / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmajor := integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi c hc ‖z‖
  apply Integrable.mono' hmajor
  · have hbase := (integrableOn_dbnHeatCosIntegrand t z).aestronglyMeasurable
    have hcosh : AEStronglyMeasurable
        (fun u : ℝ ↦ ((Real.cosh (a * u) ^ n : ℝ) : ℂ))
        (volume.restrict (Ioi 0)) :=
      (Complex.continuous_ofReal.comp
        (by fun_prop : Continuous (fun u : ℝ ↦ Real.cosh (a * u) ^ n))).aestronglyMeasurable
    exact hbase.mul hcosh
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hcosh : Real.cosh (a * u) ^ n ≤
        Real.exp ((n : ℝ) * (a * u) ^ 2 / 2) := by
      calc
        Real.cosh (a * u) ^ n ≤ (Real.exp ((a * u) ^ 2 / 2)) ^ n :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n
        _ = Real.exp ((n : ℝ) * (a * u) ^ 2 / 2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le n), norm_mul, norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (z * (u : ℂ))‖ * Real.cosh (a * u) ^ n ≤
        Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖z‖ * u) * Real.exp ((n : ℝ) * (a * u) ^ 2 / 2) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_cos_mul_real_le z hu0
      _ ≤ (1 + u ^ 2) * Real.exp (c * u ^ 2 + ‖z‖ * u) *
          ‖deBruijnNewmanPhi u‖ := by
        have hscale : (1 : ℝ) ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg u]
        have hexp :
            Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                Real.exp ((n : ℝ) * (a * u) ^ 2 / 2) =
              Real.exp (c * u ^ 2 + ‖z‖ * u) := by
          rw [Real.exp_add]
          dsimp only [c]
          rw [show (|t| + (n : ℝ) * a ^ 2 / 2) * u ^ 2 =
            |t| * u ^ 2 + (n : ℝ) * (a * u) ^ 2 / 2 by ring,
            Real.exp_add]
          ring
        calc
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
              Real.exp (‖z‖ * u) * Real.exp ((n : ℝ) * (a * u) ^ 2 / 2) =
            1 * (Real.exp (c * u ^ 2 + ‖z‖ * u) *
              ‖deBruijnNewmanPhi u‖) := by rw [← hexp]; ring
          _ ≤ (1 + u ^ 2) * (Real.exp (c * u ^ 2 + ‖z‖ * u) *
              ‖deBruijnNewmanPhi u‖) := by gcongr
          _ = _ := by ring

private def dbnCoshApprox (t a : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), dbnCoshIntegrand t a n z u

private theorem dbnCoshApprox_zero (t a : ℝ) :
    dbnCoshApprox t a 0 = deBruijnNewmanH t := by
  funext z
  rw [dbnCoshApprox, deBruijnNewmanH]
  congr 1
  funext u
  simp [dbnCoshIntegrand]

private theorem dbnCoshIntegrand_average
    (t a : ℝ) (n : ℕ) (z : ℂ) (u : ℝ) :
    (dbnCoshIntegrand t a n (z + I * (a : ℂ)) u +
      dbnCoshIntegrand t a n (z - I * (a : ℂ)) u) / 2 =
    dbnCoshIntegrand t a (n + 1) z u := by
  rw [dbnCoshIntegrand, dbnCoshIntegrand, dbnCoshIntegrand]
  let A : ℂ := ((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ)
  let C : ℂ := (Real.cosh (a * u) ^ n : ℝ)
  let cp : ℂ := Complex.cos ((z + I * (a : ℂ)) * (u : ℂ))
  let cm : ℂ := Complex.cos ((z - I * (a : ℂ)) * (u : ℂ))
  let c0 : ℂ := Complex.cos (z * (u : ℂ))
  let ch : ℂ := (Real.cosh (a * u) : ℝ)
  have htrig : (cp + cm) / 2 = c0 * ch := by
    simpa only [cp, cm, c0, ch] using cos_add_I_average z a u
  have hpow : ((Real.cosh (a * u) ^ (n + 1) : ℝ) : ℂ) = C * ch := by
    simp only [C, ch, pow_succ]
    push_cast
    rfl
  rw [hpow]
  change (A * cp * C + A * cm * C) / 2 = A * c0 * (C * ch)
  calc
    (A * cp * C + A * cm * C) / 2 = A * C * ((cp + cm) / 2) := by ring
    _ = A * C * (c0 * ch) := by rw [htrig]
    _ = A * c0 * (C * ch) := by ring

private theorem verticalAverage_dbnCoshApprox
    (t a : ℝ) (n : ℕ) (z : ℂ) :
    verticalAverage a (dbnCoshApprox t a n) z = dbnCoshApprox t a (n + 1) z := by
  have hp := integrableOn_dbn_cosh_pow_integrand t a n (z + I * (a : ℂ))
  have hm := integrableOn_dbn_cosh_pow_integrand t a n (z - I * (a : ℂ))
  have hp' : IntegrableOn (dbnCoshIntegrand t a n (z + I * (a : ℂ))) (Ioi 0) := by
    exact hp
  have hm' : IntegrableOn (dbnCoshIntegrand t a n (z - I * (a : ℂ))) (Ioi 0) := by
    exact hm
  rw [verticalAverage]
  simp only [dbnCoshApprox]
  rw [← integral_add hp' hm', ← integral_div]
  apply integral_congr_ae
  filter_upwards with u
  exact dbnCoshIntegrand_average t a n z u

private theorem verticalAverageIterate_deBruijnNewmanH
    (t a : ℝ) (n : ℕ) :
    verticalAverageIterate a n (deBruijnNewmanH t) = dbnCoshApprox t a n := by
  induction n with
  | zero => exact dbnCoshApprox_zero t a |>.symm
  | succ n hn =>
      funext z
      rw [verticalAverageIterate, hn, verticalAverage_dbnCoshApprox]

private theorem tendsto_nat_mul_cosh_sqrt_sub_one
    {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) *
        (Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) - 1))
      atTop (𝓝 (δ * u ^ 2)) := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  by_cases hu : u = 0
  · subst u
    simp
  let y : ℕ → ℝ := fun n ↦ Real.sqrt (2 * δ / (n : ℝ)) * u / 2
  have hfrac : Tendsto (fun n : ℕ ↦ 2 * δ / (n : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (2 * δ / (n : ℝ)))
      atTop (𝓝 0) := by
    rw [show (fun n : ℕ ↦ Real.sqrt (2 * δ / (n : ℝ))) =
      (fun x : ℝ ↦ Real.sqrt x) ∘ (fun n : ℕ ↦ 2 * δ / (n : ℝ)) by rfl]
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hfrac
  have hy : Tendsto y atTop (𝓝 0) := by
    simpa only [y, zero_mul, zero_div] using (hsqrt.mul_const u).div_const 2
  have hy_ne : ∀ᶠ n : ℕ in atTop, y n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    dsimp only [y]
    exact div_ne_zero
      (mul_ne_zero (Real.sqrt_ne_zero'.mpr (div_pos (mul_pos (by norm_num) hδ) hnR)) hu)
      (by norm_num)
  have hy_punctured : Tendsto y atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy, by simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hy_ne⟩
  have hratio : Tendsto (fun n : ℕ ↦ Real.sinh (y n) / y n) atTop (𝓝 1) := by
    have hslope := (Real.hasDerivAt_sinh 0).tendsto_slope_zero.comp hy_punctured
    rw [show (fun n : ℕ ↦ Real.sinh (y n) / y n) =
      (fun x : ℝ ↦ x⁻¹ * Real.sinh x) ∘ y by
        funext n
        simp only [Function.comp_apply, div_eq_mul_inv, mul_comm]]
    simpa only [zero_add, Real.sinh_zero, sub_zero, smul_eq_mul,
      Real.cosh_zero] using hslope
  have hidentity : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) - 1) =
        (Real.sinh (y n) / y n) ^ 2 * (δ * u ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hbase : 0 ≤ 2 * δ / (n : ℝ) := by positivity
    have hsqrt_sq : Real.sqrt (2 * δ / (n : ℝ)) ^ 2 =
        2 * δ / (n : ℝ) := Real.sq_sqrt hbase
    have hcosh : Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) - 1 =
        2 * Real.sinh (y n) ^ 2 := by
      rw [show Real.sqrt (2 * δ / (n : ℝ)) * u = 2 * y n by
        dsimp only [y]
        ring,
        Real.cosh_two_mul, Real.cosh_sq]
      ring
    have hy0 : y n ≠ 0 := by
      dsimp only [y]
      exact div_ne_zero
        (mul_ne_zero (Real.sqrt_ne_zero'.mpr (div_pos (mul_pos (by norm_num) hδ) hnR)) hu)
        (by norm_num)
    have hy_sq : y n ^ 2 = δ * u ^ 2 / (2 * (n : ℝ)) := by
      dsimp only [y]
      rw [div_pow, mul_pow, hsqrt_sq]
      field_simp [hnR.ne']
    calc
      (n : ℝ) * (Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) - 1) =
          2 * (n : ℝ) * Real.sinh (y n) ^ 2 := by rw [hcosh]; ring
      _ = Real.sinh (y n) ^ 2 / y n ^ 2 * (δ * u ^ 2) := by
        rw [hy_sq]
        field_simp [hnR.ne', hδ.ne', hu]
      _ = (Real.sinh (y n) / y n) ^ 2 * (δ * u ^ 2) := by
        exact congrArg (fun q : ℝ ↦ q * (δ * u ^ 2))
          (div_pow (Real.sinh (y n)) (y n) 2).symm
  have hlimit := (hratio.pow 2).mul_const (δ * u ^ 2)
  have hlimit' : Tendsto
      (fun n : ℕ ↦ (Real.sinh (y n) / y n) ^ 2 * (δ * u ^ 2))
      atTop (𝓝 (δ * u ^ 2)) := by simpa using hlimit
  exact hlimit'.congr' (hidentity.mono fun _ h ↦ h.symm)

private theorem tendsto_cosh_sqrt_pow_exp
    {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    Tendsto
      (fun n : ℕ ↦ Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n)
      atTop (𝓝 (Real.exp (δ * u ^ 2))) := by
  have hbase := tendsto_nat_mul_cosh_sqrt_sub_one hδ u
  have hmain := Real.tendsto_one_add_pow_exp_of_tendsto hbase
  have hfun :
      (fun n : ℕ ↦ (1 + (Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) - 1)) ^ n) =
        (fun n : ℕ ↦ Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n) := by
    funext n
    congr 1
    ring
  rw [hfun] at hmain
  exact hmain

private def dbnForwardApprox (t δ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dbnCoshApprox t (Real.sqrt (2 * δ / (n : ℝ))) n

private theorem cosh_sqrt_pow_le_exp
    {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) (n : ℕ) :
    Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n ≤
      Real.exp (δ * u ^ 2) := by
  cases n with
  | zero =>
      simpa using Real.one_le_exp (mul_nonneg hδ (sq_nonneg u))
  | succ n =>
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hbase : 0 ≤ 2 * δ / ((n + 1 : ℕ) : ℝ) := by positivity
      calc
        Real.cosh (Real.sqrt (2 * δ / ((n + 1 : ℕ) : ℝ)) * u) ^ (n + 1) ≤
            Real.exp ((n + 1 : ℕ) *
              (Real.sqrt (2 * δ / ((n + 1 : ℕ) : ℝ)) * u) ^ 2 / 2) := by
          calc
            _ ≤ (Real.exp
                ((Real.sqrt (2 * δ / ((n + 1 : ℕ) : ℝ)) * u) ^ 2 / 2)) ^
                (n + 1) :=
              pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
            _ = _ := by
              rw [← Real.exp_nat_mul]
              congr 1
              ring
        _ = Real.exp (δ * u ^ 2) := by
          congr 1
          rw [mul_pow, Real.sq_sqrt hbase]
          field_simp [hn.ne']

private theorem dbnForwardApprox_admissible
    {t : ℝ} (ht : deBruijnNewmanAllZerosReal t)
    (δ : ℝ) (n : ℕ) : VerticalAverageAdmissible (dbnForwardApprox t δ n) := by
  let hbase : VerticalAverageAdmissible (deBruijnNewmanH t) :=
    ⟨deBruijnNewmanH_entireOfOrderAtMost_one t,
      deBruijnNewmanH_neg t, deBruijnNewmanH_zero_ne_zero t, ht⟩
  let a : ℝ := Real.sqrt (2 * δ / (n : ℝ))
  have hiter := hbase.verticalAverageIterate (a := a) (Real.sqrt_nonneg _) n
  rw [verticalAverageIterate_deBruijnNewmanH] at hiter
  simpa only [dbnForwardApprox, a] using hiter

private theorem dbnForwardApprox_zeros_real
    {t : ℝ} (ht : deBruijnNewmanAllZerosReal t) (δ : ℝ) (n : ℕ) :
    ∀ z : ℂ, dbnForwardApprox t δ n z = 0 → z.im = 0 :=
  (dbnForwardApprox_admissible ht δ n).zeros_real

private def dbnForwardError (t δ B : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
    |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
      Real.exp (δ * u ^ 2)| * Real.exp (B * u)

private theorem norm_dbnForwardError_le
    (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (B : ℝ) (n : ℕ)
    {u : ℝ} (_hu : 0 ≤ u) :
    ‖dbnForwardError t δ B n u‖ ≤
      2 * ((1 + u ^ 2) * Real.exp ((|t| + δ) * u ^ 2 + B * u) *
        ‖deBruijnNewmanPhi u‖) := by
  have hm_nonneg : 0 ≤
      Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n :=
    pow_nonneg (Real.cosh_pos _).le n
  have hm_le := cosh_sqrt_pow_le_exp hδ u n
  have hdiff :
      |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
        Real.exp (δ * u ^ 2)| ≤ 2 * Real.exp (δ * u ^ 2) := by
    calc
      |_ - Real.exp (δ * u ^ 2)| ≤
          |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n| +
            |Real.exp (δ * u ^ 2)| := abs_sub _ _
      _ = Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n +
            Real.exp (δ * u ^ 2) := by
        rw [abs_of_nonneg hm_nonneg, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (δ * u ^ 2) + Real.exp (δ * u ^ 2) := by gcongr
      _ = 2 * Real.exp (δ * u ^ 2) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (abs_nonneg _)) (Real.exp_pos _).le)]
  have ht_exp : Real.exp (t * u ^ 2) ≤ Real.exp (|t| * u ^ 2) := by
    gcongr
    exact le_abs_self t
  calc
    dbnForwardError t δ B n u ≤
        Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (2 * Real.exp (δ * u ^ 2)) * Real.exp (B * u) := by
      dsimp only [dbnForwardError]
      gcongr
    _ = 2 * (Real.exp ((|t| + δ) * u ^ 2 + B * u) *
          ‖deBruijnNewmanPhi u‖) := by
      rw [Real.exp_add,
        show (|t| + δ) * u ^ 2 = |t| * u ^ 2 + δ * u ^ 2 by ring,
        Real.exp_add]
      ring
    _ ≤ 2 * ((1 + u ^ 2) * Real.exp ((|t| + δ) * u ^ 2 + B * u) *
          ‖deBruijnNewmanPhi u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        Real.exp ((|t| + δ) * u ^ 2 + B * u) * ‖deBruijnNewmanPhi u‖ =
            1 * (Real.exp ((|t| + δ) * u ^ 2 + B * u) *
              ‖deBruijnNewmanPhi u‖) := by ring
        _ ≤ (1 + u ^ 2) * (Real.exp ((|t| + δ) * u ^ 2 + B * u) *
              ‖deBruijnNewmanPhi u‖) := by
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [sq_nonneg u])
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        _ = _ := by ring

private theorem integrableOn_dbnForwardError
    (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (B : ℝ) (n : ℕ) :
    IntegrableOn (dbnForwardError t δ B n) (Ioi 0) := by
  let bound : ℝ → ℝ := fun u ↦
    2 * ((1 + u ^ 2) * Real.exp ((|t| + δ) * u ^ 2 + B * u) *
      ‖deBruijnNewmanPhi u‖)
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    exact (integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|t| + δ) (by positivity) B).const_mul 2
  apply Integrable.mono' hbound
  · have hbase : AEStronglyMeasurable
        (fun u : ℝ ↦ Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖)
        (volume.restrict (Ioi 0)) := by
      exact (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (t * u ^ 2))).aestronglyMeasurable.mul
        (aestronglyMeasurable_deBruijnNewmanPhi _).norm
    have hdiff : AEStronglyMeasurable
        (fun u : ℝ ↦ |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
          Real.exp (δ * u ^ 2)| * Real.exp (B * u))
        (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous (fun u : ℝ ↦
        |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
          Real.exp (δ * u ^ 2)| * Real.exp (B * u))).aestronglyMeasurable
    refine (hbase.mul hdiff).congr ?_
    filter_upwards with u
    simp only [Pi.mul_apply, dbnForwardError]
    ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    exact norm_dbnForwardError_le t hδ B n hu.le

private theorem tendsto_integral_dbnForwardError
    (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (B : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ u in Ioi (0 : ℝ), dbnForwardError t δ B n u)
      atTop (𝓝 0) := by
  let bound : ℝ → ℝ := fun u ↦
    2 * ((1 + u ^ 2) * Real.exp ((|t| + δ) * u ^ 2 + B * u) *
      ‖deBruijnNewmanPhi u‖)
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    exact (integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|t| + δ) (by positivity) B).const_mul 2
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (dbnForwardError t δ B n)
        (volume.restrict (Ioi 0)) := by
    filter_upwards with n
    exact (integrableOn_dbnForwardError t hδ B n).aestronglyMeasurable
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ᵐ u ∂volume.restrict (Ioi 0),
      ‖dbnForwardError t δ B n u‖ ≤ bound u := by
    filter_upwards with n
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    exact norm_dbnForwardError_le t hδ B n hu.le
  have hlim : ∀ᵐ u ∂volume.restrict (Ioi 0),
      Tendsto (fun n : ℕ ↦ dbnForwardError t δ B n u) atTop (𝓝 0) := by
    filter_upwards with u
    have hm := tendsto_cosh_sqrt_pow_exp hδ u
    have habs : Tendsto
        (fun n : ℕ ↦ |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
          Real.exp (δ * u ^ 2)|) atTop (𝓝 0) := by
      have habs0 := (hm.sub_const (Real.exp (δ * u ^ 2))).abs
      simpa only [sub_self, abs_zero] using habs0
    change Tendsto
      (fun n : ℕ ↦ Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
        |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
          Real.exp (δ * u ^ 2)| * Real.exp (B * u)) atTop (𝓝 0)
    simpa only [mul_zero, zero_mul] using
      (((tendsto_const_nhds.mul tendsto_const_nhds).mul habs).mul
        tendsto_const_nhds)
  have hmain := tendsto_integral_filter_of_dominated_convergence bound hmeas hdom hbound hlim
  simpa using hmain

private theorem norm_dbnForwardApprox_sub_le_errorIntegral
    (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) {B : ℝ} {z : ℂ} (hzB : ‖z‖ ≤ B)
    (n : ℕ) :
    ‖dbnForwardApprox t δ n z - deBruijnNewmanH (t + δ) z‖ ≤
      ∫ u in Ioi (0 : ℝ), dbnForwardError t δ B n u := by
  let a : ℝ := Real.sqrt (2 * δ / (n : ℝ))
  have happ : IntegrableOn (dbnCoshIntegrand t a n z) (Ioi 0) :=
    integrableOn_dbn_cosh_pow_integrand t a n z
  have htarget : IntegrableOn
      (fun u : ℝ ↦
        (((Real.exp ((t + δ) * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (Ioi 0) :=
    integrableOn_dbnHeatCosIntegrand (t + δ) z
  rw [dbnForwardApprox, dbnCoshApprox, deBruijnNewmanH]
  rw [← integral_sub happ htarget]
  apply norm_integral_le_of_norm_le (integrableOn_dbnForwardError t hδ B n)
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu0 : 0 ≤ u := hu.le
  have hexptime : Real.exp ((t + δ) * u ^ 2) =
      Real.exp (t * u ^ 2) * Real.exp (δ * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change ‖dbnCoshIntegrand t a n z u -
      (((Real.exp ((t + δ) * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ)))‖ ≤ dbnForwardError t δ B n u
  rw [dbnCoshIntegrand, dbnForwardError, hexptime]
  have hfactor :
      (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)) * (Real.cosh (a * u) ^ n : ℝ)) -
        (((Real.exp (t * u ^ 2) * Real.exp (δ * u ^ 2) *
          deBruijnNewmanPhi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))) =
      (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))) *
        ((Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
          Real.exp (δ * u ^ 2) : ℝ) : ℂ) := by
    dsimp only [a]
    push_cast
    ring
  rw [hfactor]
  rw [norm_mul, norm_mul, norm_real, norm_real]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  change Real.exp (t * u ^ 2) * |deBruijnNewmanPhi u| *
      ‖Complex.cos (z * (u : ℂ))‖ *
        |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
          Real.exp (δ * u ^ 2)| ≤
    Real.exp (t * u ^ 2) * |deBruijnNewmanPhi u| *
      |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
        Real.exp (δ * u ^ 2)| * Real.exp (B * u)
  have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (B * u) := by
    calc
      ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (‖z‖ * u) :=
        norm_complex_cos_mul_real_le z hu0
      _ ≤ Real.exp (B * u) := by
        gcongr
  calc
    Real.exp (t * u ^ 2) * |deBruijnNewmanPhi u| *
          ‖Complex.cos (z * (u : ℂ))‖ *
            |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
              Real.exp (δ * u ^ 2)| ≤
        Real.exp (t * u ^ 2) * |deBruijnNewmanPhi u| * Real.exp (B * u) *
            |Real.cosh (Real.sqrt (2 * δ / (n : ℝ)) * u) ^ n -
              Real.exp (δ * u ^ 2)| := by gcongr
    _ = _ := by ring

private theorem deBruijnNewmanAllZerosReal_add
    {t δ : ℝ} (hδ : 0 ≤ δ) (ht : deBruijnNewmanAllZerosReal t) :
    deBruijnNewmanAllZerosReal (t + δ) := by
  intro z₀ hz₀
  by_contra hz₀_im
  obtain ⟨R, hR, hboundary, hnonreal⟩ :=
    exists_deBruijnNewmanH_isolating_nonreal_closedBall hz₀_im
      (t := t + δ)
  have hsphere_nonempty : (Metric.sphere z₀ R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hnorm_cont : ContinuousOn (fun z : ℂ ↦ ‖deBruijnNewmanH (t + δ) z‖)
      (Metric.sphere z₀ R) :=
    (differentiable_deBruijnNewmanH (t + δ)).continuous.norm.continuousOn
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_sphere z₀ R).exists_isMinOn hsphere_nonempty hnorm_cont
  let m : ℝ := ‖deBruijnNewmanH (t + δ) x‖
  have hm : 0 < m := norm_pos_iff.mpr (hboundary x hx)
  let B : ℝ := ‖z₀‖ + R
  have hsphere_bound : ∀ z ∈ Metric.sphere z₀ R, ‖z‖ ≤ B := by
    intro z hz
    have hdist : ‖z - z₀‖ = R := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp hz
    dsimp only [B]
    calc
      ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; ring
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ = ‖z₀‖ + R := by rw [hdist]; ring
  have hz₀_bound : ‖z₀‖ ≤ B := by
    dsimp only [B]
    linarith
  have herr : ∀ᶠ n : ℕ in atTop,
      (∫ u in Ioi (0 : ℝ), dbnForwardError t δ B n u) < m / 2 := by
    exact (tendsto_integral_dbnForwardError t hδ B).eventually
      (Iio_mem_nhds (half_pos hm))
  have hpersist : ∀ᶠ n : ℕ in atTop,
      ∃ z ∈ Metric.closedBall z₀ R, dbnForwardApprox t δ n z = 0 := by
    filter_upwards [herr] with n hn
    have hclose : ∀ z ∈ Metric.sphere z₀ R,
        ‖dbnForwardApprox t δ n z - deBruijnNewmanH (t + δ) z‖ < m / 2 := by
      intro z hz
      exact (norm_dbnForwardApprox_sub_le_errorIntegral t hδ
        (hsphere_bound z hz) n).trans_lt hn
    have hcenter_small : ‖dbnForwardApprox t δ n z₀‖ < m / 2 := by
      have hcenter := norm_dbnForwardApprox_sub_le_errorIntegral t hδ hz₀_bound n
      rw [hz₀, sub_zero] at hcenter
      exact hcenter.trans_lt hn
    by_contra hexists
    have hzero_free : ∀ z ∈ Metric.closedBall z₀ R,
        dbnForwardApprox t δ n z ≠ 0 := by
      intro z hz hzero
      exact hexists ⟨z, hz, hzero⟩
    have hdiff := (dbnForwardApprox_admissible ht δ n).order_one.differentiable
    have hanalytic : AnalyticOnNhd ℂ (dbnForwardApprox t δ n)
        (Metric.closedBall z₀ R) := fun z _ ↦ hdiff.analyticAt z
    have hanalytic_abs : AnalyticOnNhd ℂ (dbnForwardApprox t δ n)
        (Metric.closedBall z₀ |R|) := by
      simpa [abs_of_pos hR] using hanalytic
    have hnorm_boundary : ∀ z ∈ Metric.sphere z₀ R,
        m / 2 < ‖dbnForwardApprox t δ n z‖ := by
      intro z hz
      have hmin : m ≤ ‖deBruijnNewmanH (t + δ) z‖ := hxmin hz
      have htriangle : ‖deBruijnNewmanH (t + δ) z‖ ≤
          ‖dbnForwardApprox t δ n z - deBruijnNewmanH (t + δ) z‖ +
            ‖dbnForwardApprox t δ n z‖ := by
        calc
          ‖deBruijnNewmanH (t + δ) z‖ =
              ‖(deBruijnNewmanH (t + δ) z - dbnForwardApprox t δ n z) +
                dbnForwardApprox t δ n z‖ := by congr 1; ring
          _ ≤ ‖deBruijnNewmanH (t + δ) z - dbnForwardApprox t δ n z‖ +
              ‖dbnForwardApprox t δ n z‖ := norm_add_le _ _
          _ = ‖dbnForwardApprox t δ n z - deBruijnNewmanH (t + δ) z‖ +
              ‖dbnForwardApprox t δ n z‖ := by rw [norm_sub_rev]
      nlinarith [hclose z hz]
    have hcircle : CircleIntegrable
        (fun z : ℂ ↦ Real.log ‖dbnForwardApprox t δ n z‖) z₀ R :=
      (hanalytic_abs.mono Metric.sphere_subset_closedBall).meromorphicOn
        |>.circleIntegrable_log_norm
    have hlog_boundary : ∀ z ∈ Metric.sphere z₀ |R|,
        Real.log (m / 2) ≤ Real.log ‖dbnForwardApprox t δ n z‖ := by
      intro z hz
      have hz' : z ∈ Metric.sphere z₀ R := by simpa [abs_of_pos hR] using hz
      have hnorm := hnorm_boundary z hz'
      have hnorm_pos : 0 < ‖dbnForwardApprox t δ n z‖ := (half_pos hm).trans hnorm
      exact Real.strictMonoOn_log.monotoneOn (half_pos hm) hnorm_pos hnorm.le
    have havg_lower : Real.log (m / 2) ≤
        circleAverage (fun z : ℂ ↦ Real.log ‖dbnForwardApprox t δ n z‖) z₀ R := by
      calc
        Real.log (m / 2) = circleAverage (fun _ : ℂ ↦ Real.log (m / 2)) z₀ R :=
          (circleAverage_const _ _ _).symm
        _ ≤ circleAverage (fun z : ℂ ↦ Real.log ‖dbnForwardApprox t δ n z‖) z₀ R :=
          circleAverage_mono (circleIntegrable_const _ _ _) hcircle hlog_boundary
    have hcenter_ne : dbnForwardApprox t δ n z₀ ≠ 0 :=
      hzero_free z₀ (Metric.mem_closedBall_self hR.le)
    have hcenter_log : Real.log ‖dbnForwardApprox t δ n z₀‖ < Real.log (m / 2) :=
      Real.log_lt_log (norm_pos_iff.mpr hcenter_ne) hcenter_small
    have hzero_free_abs : ∀ z ∈ Metric.closedBall z₀ |R|,
        dbnForwardApprox t δ n z ≠ 0 := by
      simpa [abs_of_pos hR] using hzero_free
    rw [hanalytic_abs.circleAverage_log_norm_of_ne_zero hzero_free_abs] at havg_lower
    exact (not_lt_of_ge havg_lower) hcenter_log
  obtain ⟨n, hn⟩ := hpersist.exists
  obtain ⟨z, hzball, hzero⟩ := hn
  exact hnonreal z hzball (dbnForwardApprox_zeros_real ht δ n z hzero)

theorem deBruijnNewmanAllZerosReal_mono
    {t tau : ℝ} (htt : t ≤ tau)
    (ht : deBruijnNewmanAllZerosReal t) :
    deBruijnNewmanAllZerosReal tau := by
  have hδ : 0 ≤ tau - t := sub_nonneg.mpr htt
  have hadd := deBruijnNewmanAllZerosReal_add hδ ht
  convert hadd using 1
  ring

end

end LeanLab.Riemann
