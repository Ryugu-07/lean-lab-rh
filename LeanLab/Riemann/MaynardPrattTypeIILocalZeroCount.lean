import LeanLab.Riemann.MaynardPrattTypeIIPacking
import LeanLab.Riemann.LevinsonMontgomeryLogDerivMassBridge

set_option linter.style.header false

/-!
# A logarithmic-derivative producer for the Type-II local zero count

This file injects the finite multiplicity-bearing Type-II population into the global xi
divisor. It then charges a short ordinate window to the positive reciprocal zero mass at
`2 + i*t`. The remaining analytic task is an explicit upper bound for that logarithmic
derivative on the Euler-product line.
-/

namespace LeanLab.Riemann

open Complex Filter Function Set
open scoped BigOperators LSeries.notation

noncomputable section

/-- A Type-II multiplicity copy as the corresponding global xi divisor index. -/
def maynardPrattTypeIIToDivisorZeroIndex
    (T sigma : ℝ) :
    MaynardPrattTypeIIZeroIndex T sigma → RiemannXiDivisorZeroIndex :=
  fun i =>
    ⟨⟨i.1.1,
      ⟨i.2.1, by
        rw [riemannXi_divisor_toNat_eq_zeroMultiplicity]
        exact i.2.2⟩⟩,
      ne_zero_of_isNontrivialZero
        ((mem_maynardPrattTypeIIZeroFinset.mp i.1.2).1)⟩

@[simp] theorem maynardPrattTypeIIToDivisorZeroIndex_value
    (T sigma : ℝ) (i : MaynardPrattTypeIIZeroIndex T sigma) :
    riemannXiDivisorZeroValue
        (maynardPrattTypeIIToDivisorZeroIndex T sigma i) =
      maynardPrattTypeIIZeroValue T sigma i := by
  rfl

theorem injective_maynardPrattTypeIIToDivisorZeroIndex
    (T sigma : ℝ) :
    Function.Injective (maynardPrattTypeIIToDivisorZeroIndex T sigma) := by
  intro i j hij
  rcases i with ⟨rho, k⟩
  rcases j with ⟨tau, l⟩
  have hvalue : rho.1 = tau.1 :=
    congrArg riemannXiDivisorZeroValue hij
  have hrho : rho = tau := Subtype.ext hvalue
  subst tau
  have hindex :
      k.1 = l.1 :=
    congrArg
      (fun p : RiemannXiDivisorZeroIndex => p.1.2.1) hij
  have hfin : k = l := Fin.ext hindex
  subst l
  rfl

/-- The preceding injection bundled as a finite-set embedding. -/
def maynardPrattTypeIIToDivisorZeroEmbedding
    (T sigma : ℝ) :
    MaynardPrattTypeIIZeroIndex T sigma ↪ RiemannXiDivisorZeroIndex where
  toFun := maynardPrattTypeIIToDivisorZeroIndex T sigma
  inj' := injective_maynardPrattTypeIIToDivisorZeroIndex T sigma

theorem riemannXi_ne_zero_two_add_mul_I (t : ℝ) :
    riemannXi ((2 : ℂ) + t * I) ≠ 0 := by
  intro hzero
  have hnontrivial :
      IsNontrivialZero ((2 : ℂ) + t * I) :=
    (isNontrivialZero_iff_riemannXi_eq_zero
      ((2 : ℂ) + t * I)).mpr hzero
  have hre := nontrivial_zero_re_lt_one hnontrivial
  norm_num at hre

/-- Every paired reciprocal term is nonnegative on the line `Re(s)=2`. -/
theorem levinsonMontgomeryPairedReciprocalTerm_two_nonneg
    (t : ℝ) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ levinsonMontgomeryPairedReciprocalTerm
      ((2 : ℂ) + t * I) p := by
  let rho := riemannXiDivisorZeroValue p
  have hrho : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hrePos : 0 < rho.re := speiser_nontrivial_zero_re_pos hrho
  have hreLt : rho.re < 1 := nontrivial_zero_re_lt_one hrho
  have hfirst :
      0 ≤ (1 / (((2 : ℂ) + t * I) - rho)).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg
    · norm_num [Complex.add_re, Complex.mul_re]
      linarith
    · exact Complex.normSq_nonneg _
  have hsecond :
      0 ≤
        (1 / (((2 : ℂ) + t * I) -
          riemannXiDivisorZeroValue
            (levinsonMontgomeryPairedZeroEquiv p))).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg
    · rw [levinsonMontgomeryPairedZeroEquiv_val]
      norm_num [Complex.add_re, Complex.mul_re]
      linarith
    · exact Complex.normSq_nonneg _
  rw [levinsonMontgomeryPairedReciprocalTerm]
  rw [Complex.add_re]
  apply div_nonneg
  · exact add_nonneg hfirst hsecond
  norm_num

/-- One nearby divisor copy contributes a fixed positive amount to the paired reciprocal
mass on `Re(s)=2`. -/
theorem one_div_two_mul_four_add_sq_le_pairedReciprocalTerm
    {t H : ℝ} (hH : 0 ≤ H) (p : RiemannXiDivisorZeroIndex)
    (hnear : |(riemannXiDivisorZeroValue p).im - t| < H) :
    1 / (2 * (4 + H ^ 2)) ≤
      levinsonMontgomeryPairedReciprocalTerm
        ((2 : ℂ) + t * I) p := by
  let rho := riemannXiDivisorZeroValue p
  let a : ℝ := 2 - rho.re
  let d : ℝ := t - rho.im
  have hrho : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hrePos : 0 < rho.re := speiser_nontrivial_zero_re_pos hrho
  have hreLt : rho.re < 1 := nontrivial_zero_re_lt_one hrho
  have haOne : 1 ≤ a := by
    dsimp only [a]
    linarith
  have haTwo : a ≤ 2 := by
    dsimp only [a]
    linarith
  have hdAbs : |d| ≤ H := by
    dsimp only [d]
    simpa only [abs_sub_comm] using hnear.le
  have haSq : a ^ 2 ≤ 2 ^ 2 :=
    (sq_le_sq₀ (by linarith) (by norm_num)).mpr haTwo
  have hdSq : d ^ 2 ≤ H ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg d) hH).mpr hdAbs
  have hdenPos : 0 < a ^ 2 + d ^ 2 := by
    nlinarith [sq_nonneg d]
  have hdenLe : a ^ 2 + d ^ 2 ≤ 4 + H ^ 2 := by
    nlinarith
  have hbigPos : 0 < 4 + H ^ 2 := by positivity
  have hfrac :
      1 / (4 + H ^ 2) ≤ a / (a ^ 2 + d ^ 2) := by
    rw [div_le_div_iff₀ hbigPos hdenPos]
    nlinarith [sq_nonneg a, sq_nonneg d]
  have hfirst :
      (1 / (((2 : ℂ) + t * I) - rho)).re =
        a / (a ^ 2 + d ^ 2) := by
    rw [one_div, Complex.inv_re]
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, a, d, pow_two]
  have hsecondNonneg :
      0 ≤
        (1 / (((2 : ℂ) + t * I) -
          riemannXiDivisorZeroValue
            (levinsonMontgomeryPairedZeroEquiv p))).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg
    · rw [levinsonMontgomeryPairedZeroEquiv_val]
      norm_num [Complex.add_re, Complex.mul_re]
      linarith
    · exact Complex.normSq_nonneg _
  rw [levinsonMontgomeryPairedReciprocalTerm, Complex.add_re, hfirst]
  calc
    1 / (2 * (4 + H ^ 2)) =
        (1 / (4 + H ^ 2)) / 2 := by
      field_simp [ne_of_gt hbigPos]
    _ ≤ (a / (a ^ 2 + d ^ 2)) / 2 := by gcongr
    _ ≤
        (a / (a ^ 2 + d ^ 2) +
          (1 / (((2 : ℂ) + t * I) -
            riemannXiDivisorZeroValue
              (levinsonMontgomeryPairedZeroEquiv p))).re) / 2 := by
      exact div_le_div_of_nonneg_right
        (le_add_of_nonneg_right hsecondNonneg) (by norm_num)

/-- The fixed absolute mass of the von Mangoldt L-series on `Re(s)=2`. -/
def maynardPrattVonMangoldtLSeriesMass : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term
      (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
      (2 : ℂ) n‖

theorem summable_maynardPrattVonMangoldtLSeriesMass :
    Summable (fun n : ℕ =>
      ‖LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (2 : ℂ) n‖) := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (by norm_num)).norm

theorem norm_vonMangoldtLSeries_two_add_mul_I_le_mass
    (t : ℝ) :
    ‖L ↗ArithmeticFunction.vonMangoldt ((2 : ℂ) + t * I)‖ ≤
      maynardPrattVonMangoldtLSeriesMass := by
  let f : ℕ → ℂ :=
    fun m => (ArithmeticFunction.vonMangoldt m : ℂ)
  have hsum :
      Summable (fun n : ℕ =>
        LSeries.term f ((2 : ℂ) + t * I) n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hpoint :
      ∀ n : ℕ,
        ‖LSeries.term f ((2 : ℂ) + t * I) n‖ ≤
          ‖LSeries.term f (2 : ℂ) n‖ := by
    intro n
    exact LSeries.norm_term_le_of_re_le_re f (by norm_num) n
  rw [show L ↗ArithmeticFunction.vonMangoldt
      ((2 : ℂ) + t * I) =
      ∑' n : ℕ, LSeries.term f ((2 : ℂ) + t * I) n by rfl]
  calc
    ‖∑' n : ℕ, LSeries.term f ((2 : ℂ) + t * I) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term f ((2 : ℂ) + t * I) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f (2 : ℂ) n‖ :=
      hsum.norm.tsum_le_tsum hpoint
        summable_maynardPrattVonMangoldtLSeriesMass
    _ = maynardPrattVonMangoldtLSeriesMass := by
      rfl

theorem logDeriv_GammaR_two_add_mul_I_re_le
    (t : ℝ) :
    (logDeriv Gammaℝ ((2 : ℂ) + t * I)).re ≤
      Real.log (|t| + 2) + 1 := by
  let s : ℂ := (2 : ℂ) + t * I
  let z : ℂ := s / 2
  have hzRe : z.re = 1 := by
    norm_num [z, s, Complex.add_re, Complex.mul_re]
  have hzRePos : 0 < z.re := by rw [hzRe]; norm_num
  have hzNormLower : 1 ≤ ‖z‖ := by
    calc
      1 = |z.re| := by rw [hzRe]; norm_num
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hzNormLower
  have hzNormUpper : ‖z‖ ≤ |t| + 2 := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| :=
        Complex.norm_le_abs_re_add_abs_im z
      _ = 1 + |t| / 2 := by
        rw [hzRe]
        norm_num [z, s, Complex.add_im, Complex.mul_im, abs_div]
      _ ≤ |t| + 2 := by
        nlinarith [abs_nonneg t]
  have htargetPos : 0 < |t| + 2 := by positivity
  have hlog :
      Real.log ‖z‖ ≤ Real.log (|t| + 2) :=
    Real.log_le_log hzNormPos hzNormUpper
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder z
  have hRnorm :
      ‖R‖ ≤ 27 / (64 * ‖z‖ ^ 2) :=
    levinsonMontgomery_digamma_stirling_remainder_norm_le hzRePos
  have hRle : ‖R‖ ≤ 1 := by
    refine hRnorm.trans ?_
    have hzSq : 1 ≤ ‖z‖ ^ 2 :=
      by
        simpa using
          (sq_le_sq₀ (by norm_num) (norm_nonneg z)).mpr hzNormLower
    have hden : 0 < 64 * ‖z‖ ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hRreal : R.re ≤ 1 :=
    (le_abs_self R.re).trans (Complex.abs_re_le_norm R) |>.trans hRle
  have hinvNorm :
      ‖1 / (2 * z)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_mul]
    norm_num
    exact inv_le_one_of_one_le₀ hzNormLower
  have hinvReal :
      -(1 / (2 * z)).re ≤ 1 / 2 := by
    exact (neg_le_abs (1 / (2 * z)).re).trans
      ((Complex.abs_re_le_norm _).trans hinvNorm)
  have hdigamma := levinsonMontgomery_digamma_stirling hzRePos
  change Complex.digamma z = Complex.log z - 1 / (2 * z) + R at hdigamma
  have hdigammaReal := congrArg Complex.re hdigamma
  simp only [Complex.add_re, Complex.sub_re, Complex.log_re] at hdigammaReal
  have hdigammaUpper :
      (Complex.digamma z).re ≤ Real.log (|t| + 2) + 2 := by
    linarith
  have hdigammaUpperS :
      (Complex.digamma (s / 2)).re ≤ Real.log (|t| + 2) + 2 := by
    simpa only [z] using hdigammaUpper
  have hgamma := logDeriv_GammaR_eq_digamma
    (s := s) (by norm_num [s, Complex.add_re, Complex.mul_re])
  have hgammaReal := congrArg Complex.re hgamma
  have hlogPiNonneg : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogTargetNonneg : 0 ≤ Real.log (|t| + 2) :=
    Real.log_nonneg (by nlinarith [abs_nonneg t])
  norm_num [s] at hgammaReal ⊢
  linarith

/-- A fixed constant in the right-half-plane xi logarithmic-derivative bound. -/
def maynardPrattXiLogDerivConstant : ℝ :=
  3 + maynardPrattVonMangoldtLSeriesMass

theorem logDeriv_riemannXi_two_add_mul_I_re_le
    (t : ℝ) :
    (logDeriv riemannXi ((2 : ℂ) + t * I)).re ≤
      Real.log (|t| + 2) + maynardPrattXiLogDerivConstant := by
  have hdecomp :=
    logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
      (s := ((2 : ℂ) + t * I)) (by norm_num)
  have hpole0 :
      (1 / ((2 : ℂ) + t * I)).re ≤ 1 := by
    rw [one_div, Complex.inv_re]
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    have hden : 0 < 4 + t * t := by nlinarith [sq_nonneg t]
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg t]
  have hpole1 :
      (1 / (((2 : ℂ) + t * I) - 1)).re ≤ 1 := by
    rw [one_div, Complex.inv_re]
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
  have hgamma := logDeriv_GammaR_two_add_mul_I_re_le t
  have hprime :
      -((L ↗ArithmeticFunction.vonMangoldt
        ((2 : ℂ) + t * I)).re) ≤
        maynardPrattVonMangoldtLSeriesMass := by
    exact (neg_le_abs _).trans
      ((Complex.abs_re_le_norm _).trans
        (norm_vonMangoldtLSeries_two_add_mul_I_le_mass t))
  have hreal := congrArg Complex.re hdecomp
  simp only [Complex.add_re, Complex.sub_re] at hreal
  rw [maynardPrattXiLogDerivConstant]
  linarith

/-- The embedded divisor copies in one Type-II local window. -/
def maynardPrattTypeIILocalDivisorFinset
    (T sigma H : ℝ) (center : MaynardPrattTypeIIZeroIndex T sigma) :
    Finset RiemannXiDivisorZeroIndex :=
  (Finset.univ.filter fun i : MaynardPrattTypeIIZeroIndex T sigma =>
      |(maynardPrattTypeIIZeroValue T sigma i).im -
        (maynardPrattTypeIIZeroValue T sigma center).im| < H).map
    (maynardPrattTypeIIToDivisorZeroEmbedding T sigma)

theorem card_maynardPrattTypeIILocalDivisorFinset
    (T sigma H : ℝ) (center : MaynardPrattTypeIIZeroIndex T sigma) :
    (maynardPrattTypeIILocalDivisorFinset T sigma H center).card =
      maynardPrattTypeIILocalMultiplicityCount T sigma H center := by
  simp [maynardPrattTypeIILocalDivisorFinset,
    maynardPrattTypeIILocalMultiplicityCount]

/-- A Type-II local multiplicity count is bounded by the actual positive xi reciprocal
mass on `Re(s)=2`. -/
theorem localMultiplicityCount_div_le_realPairedZeroSum
    (T sigma : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (center : MaynardPrattTypeIIZeroIndex T sigma) :
    (maynardPrattTypeIILocalMultiplicityCount T sigma H center : ℝ) /
        (2 * (4 + H ^ 2)) ≤
      levinsonMontgomeryRealPairedZeroSum
        ((2 : ℂ) +
          (maynardPrattTypeIIZeroValue T sigma center).im * I) := by
  let t : ℝ := (maynardPrattTypeIIZeroValue T sigma center).im
  let S : Finset RiemannXiDivisorZeroIndex :=
    maynardPrattTypeIILocalDivisorFinset T sigma H center
  have hxi : riemannXi ((2 : ℂ) + t * I) ≠ 0 :=
    riemannXi_ne_zero_two_add_mul_I t
  have hsum :
      Summable (levinsonMontgomeryPairedReciprocalTerm
        ((2 : ℂ) + t * I)) :=
    summable_levinsonMontgomeryPairedReciprocalTerm hxi
  have hterm :
      ∀ p ∈ S,
        1 / (2 * (4 + H ^ 2)) ≤
          levinsonMontgomeryPairedReciprocalTerm
            ((2 : ℂ) + t * I) p := by
    intro p hp
    change p ∈
      maynardPrattTypeIILocalDivisorFinset T sigma H center at hp
    rw [maynardPrattTypeIILocalDivisorFinset, Finset.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have hnear :
        |(riemannXiDivisorZeroValue
            (maynardPrattTypeIIToDivisorZeroIndex T sigma i)).im - t| < H := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        maynardPrattTypeIIToDivisorZeroIndex_value, t] using hi
    exact one_div_two_mul_four_add_sq_le_pairedReciprocalTerm hH _ hnear
  calc
    (maynardPrattTypeIILocalMultiplicityCount T sigma H center : ℝ) /
        (2 * (4 + H ^ 2)) =
        ∑ _p ∈ S, 1 / (2 * (4 + H ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_maynardPrattTypeIILocalDivisorFinset]
      ring
    _ ≤ ∑ p ∈ S,
        levinsonMontgomeryPairedReciprocalTerm
          ((2 : ℂ) + t * I) p := Finset.sum_le_sum hterm
    _ ≤ ∑' p,
        levinsonMontgomeryPairedReciprocalTerm
          ((2 : ℂ) + t * I) p :=
      hsum.sum_le_tsum S
        (fun p _ => levinsonMontgomeryPairedReciprocalTerm_two_nonneg t p)
    _ = levinsonMontgomeryRealPairedZeroSum ((2 : ℂ) + t * I) := by
      rfl

/-- The local count bridge expressed directly through the actual xi logarithmic
derivative. -/
theorem localMultiplicityCount_div_le_logDeriv_riemannXi_re
    (T sigma : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (center : MaynardPrattTypeIIZeroIndex T sigma) :
    (maynardPrattTypeIILocalMultiplicityCount T sigma H center : ℝ) /
        (2 * (4 + H ^ 2)) ≤
      (logDeriv riemannXi
        ((2 : ℂ) +
          (maynardPrattTypeIIZeroValue T sigma center).im * I)).re := by
  rw [← levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re
    (riemannXi_ne_zero_two_add_mul_I
      (maynardPrattTypeIIZeroValue T sigma center).im)]
  exact localMultiplicityCount_div_le_realPairedZeroSum T sigma hH center

/-- The unconditional local count bound before specializing the window and height scales. -/
theorem localMultiplicityCount_le_log_bound
    (T sigma : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (center : MaynardPrattTypeIIZeroIndex T sigma) :
    (maynardPrattTypeIILocalMultiplicityCount T sigma H center : ℝ) ≤
      2 * (4 + H ^ 2) *
        (Real.log
          (|(maynardPrattTypeIIZeroValue T sigma center).im| + 2) +
            maynardPrattXiLogDerivConstant) := by
  let t : ℝ := (maynardPrattTypeIIZeroValue T sigma center).im
  have hfactor : 0 < 2 * (4 + H ^ 2) := by positivity
  have hdiv :=
    localMultiplicityCount_div_le_logDeriv_riemannXi_re
      T sigma hH center
  have hlog := logDeriv_riemannXi_two_add_mul_I_re_le t
  have hscaled :=
    (div_le_iff₀ hfactor).mp (hdiv.trans hlog)
  simpa only [t] using hscaled.trans_eq (by ring)

/-- At the literal Maynard--Pratt packing radius, every Type-II local window has a uniform
polylogarithmic multiplicity bound. -/
theorem eventually_maynardPrattTypeIILocalMultiplicityCount_source_le :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (sigma : ℝ) (center : MaynardPrattTypeIIZeroIndex T sigma),
        maynardPrattTypeIILocalMultiplicityCount
            T sigma (Real.log T ^ (3 : ℕ)) center ≤
          Nat.ceil (30 * Real.log T ^ (7 : ℕ)) := by
  let C : ℝ := maynardPrattXiLogDerivConstant
  filter_upwards [
    eventually_ge_atTop (Real.exp (max C 3))] with T hTlarge
  intro sigma center
  have hmaxNonneg : 0 ≤ max C 3 :=
    zero_le_three.trans (le_max_right C 3)
  have hTpos : 0 < T :=
    (Real.exp_pos (max C 3)).trans_le hTlarge
  have hlogLower : max C 3 ≤ Real.log T := by
    calc
      max C 3 = Real.log (Real.exp (max C 3)) := by
        rw [Real.log_exp]
      _ ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos _) hTlarge
  have hlogThree : 3 ≤ Real.log T :=
    (le_max_right C 3).trans hlogLower
  have hC : C ≤ Real.log T :=
    (le_max_left C 3).trans hlogLower
  have hTfour : 4 ≤ T := by
    calc
      (4 : ℝ) = 1 + 3 := by norm_num
      _ ≤ Real.exp 3 := by
        simpa [add_comm] using Real.add_one_le_exp 3
      _ ≤ Real.exp (max C 3) :=
        Real.exp_le_exp.mpr (le_max_right C 3)
      _ ≤ T := hTlarge
  have hmem :=
    mem_maynardPrattTypeIIZeroFinset.mp center.1.2
  let t : ℝ := (maynardPrattTypeIIZeroValue T sigma center).im
  have htLower : T ≤ t := by
    simpa only [t, maynardPrattTypeIIZeroValue] using hmem.2.2.1
  have htUpper : t ≤ 2 * T := by
    simpa only [t, maynardPrattTypeIIZeroValue] using hmem.2.2.2.1
  have htPos : 0 < t := hTpos.trans_le htLower
  have htTwo : t + 2 ≤ T ^ 2 := by
    nlinarith [sq_nonneg (T - 2)]
  have hlogHeight :
      Real.log (|t| + 2) ≤ 2 * Real.log T := by
    rw [abs_of_pos htPos]
    calc
      Real.log (t + 2) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by linarith) htTwo
      _ = 2 * Real.log T := by
        rw [Real.log_pow]
        norm_num
  have hlogFactor :
      Real.log (|t| + 2) + C ≤ 3 * Real.log T := by
    linarith
  have hlogPos : 0 < Real.log T := by linarith
  have hlogSixOne : 1 ≤ Real.log T ^ (6 : ℕ) := by
    have hone : 1 ≤ Real.log T := by linarith
    exact one_le_pow₀ hone
  have hwindowFactor :
      2 * (4 + (Real.log T ^ (3 : ℕ)) ^ 2) ≤
        10 * Real.log T ^ (6 : ℕ) := by
    have hpow :
        (Real.log T ^ (3 : ℕ)) ^ 2 =
          Real.log T ^ (6 : ℕ) := by ring
    rw [hpow]
    nlinarith
  have hcount :=
    localMultiplicityCount_le_log_bound
      T sigma (show 0 ≤ Real.log T ^ (3 : ℕ) by positivity) center
  have hcountReal :
      (maynardPrattTypeIILocalMultiplicityCount
          T sigma (Real.log T ^ (3 : ℕ)) center : ℝ) ≤
        30 * Real.log T ^ (7 : ℕ) := by
    calc
      (maynardPrattTypeIILocalMultiplicityCount
          T sigma (Real.log T ^ (3 : ℕ)) center : ℝ) ≤
          2 * (4 + (Real.log T ^ (3 : ℕ)) ^ 2) *
            (Real.log (|t| + 2) + C) := by
        simpa only [t, C] using hcount
      _ ≤ (10 * Real.log T ^ (6 : ℕ)) *
          (3 * Real.log T) := by
        exact mul_le_mul hwindowFactor hlogFactor
          (by
            have hxiUpperNonneg :
                0 ≤ Real.log (|t| + 2) + C := by
              exact (localMultiplicityCount_div_le_logDeriv_riemannXi_re
                T sigma
                (show 0 ≤ Real.log T ^ (3 : ℕ) by positivity)
                center).trans
                (logDeriv_riemannXi_two_add_mul_I_re_le t) |>.trans'
                (by positivity)
            exact hxiUpperNonneg)
          (by positivity)
      _ = 30 * Real.log T ^ (7 : ℕ) := by ring
  have hceil :
      (maynardPrattTypeIILocalMultiplicityCount
          T sigma (Real.log T ^ (3 : ℕ)) center : ℝ) ≤
        (Nat.ceil (30 * Real.log T ^ (7 : ℕ)) : ℝ) :=
    hcountReal.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The local zero-count producer composed with the multiplicity-aware finite packing
theorem. -/
theorem eventually_exists_maynardPrattTypeIISeparated_source_card_control :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ sigma : ℝ,
        ∃ S : Finset (MaynardPrattTypeIIZeroIndex T sigma),
          IsOrdinateSeparated S
              (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
              (Real.log T ^ (3 : ℕ)) ∧
          IsOrdinateCover S Finset.univ
              (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
              (Real.log T ^ (3 : ℕ)) ∧
          maynardPrattTypeIIZeroCount T sigma ≤
            Nat.ceil (30 * Real.log T ^ (7 : ℕ)) * S.card := by
  filter_upwards [
    eventually_maynardPrattTypeIILocalMultiplicityCount_source_le,
    eventually_ge_atTop (Real.exp 1)] with T hlocal hT
  intro sigma
  have hlogPos : 0 < Real.log T := by
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
    have hlogOne : 1 ≤ Real.log T := by
      calc
        (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT
    linarith
  exact exists_maynardPrattTypeIISeparated_card_control
    T sigma (show 0 < Real.log T ^ (3 : ℕ) by positivity)
    (fun center => hlocal sigma center)

end

end LeanLab.Riemann
