import LeanLab.Riemann.ClassicalZeroDetectorDyadicDichotomy
import LeanLab.Riemann.PairCorrelationHorizontalMultiplicity
import LeanLab.Riemann.BalazardSaias

set_option linter.style.header false

/-!
# Maynard--Pratt Type-II rarity

This file starts the multiplicity-bearing reconstruction of Maynard--Pratt Lemma 24. It keeps
the actual shifted Mellin integral from the compiled classical detector and rewrites its norm
on the shifted line as critical-line mollifier--zeta mass.
-/

namespace LeanLab.Riemann

open Complex Filter Function MeasureTheory Set
open scoped Topology

noncomputable section

/-- Distinct source-range Type-II zero values. Analytic multiplicity is added by the index type
below rather than by duplicating values in this finset. -/
def maynardPrattTypeIIZeroFinset (T sigma : ℝ) : Finset ℂ :=
  by
    classical
    exact (pccPositiveZetaZeroFinset (2 * T)).filter fun rho =>
      T ≤ rho.im ∧ sigma ≤ rho.re ∧
        ClassicalDetectorTypeII
          (classicalDetectorSourceM T) (classicalDetectorSourceY T) rho

@[simp] theorem mem_maynardPrattTypeIIZeroFinset
    {T sigma : ℝ} {rho : ℂ} :
    rho ∈ maynardPrattTypeIIZeroFinset T sigma ↔
      IsNontrivialZero rho ∧
      0 < rho.im ∧ T ≤ rho.im ∧ rho.im ≤ 2 * T ∧
      sigma ≤ rho.re ∧
      ClassicalDetectorTypeII
        (classicalDetectorSourceM T) (classicalDetectorSourceY T) rho := by
  classical
  rw [maynardPrattTypeIIZeroFinset, Finset.mem_filter,
    mem_pccPositiveZetaZeroFinset]
  tauto

/-- One index for every analytic-multiplicity copy of a source-range Type-II zero. -/
abbrev MaynardPrattTypeIIZeroIndex (T sigma : ℝ) :=
  Σ rho : {rho // rho ∈ maynardPrattTypeIIZeroFinset T sigma},
    Fin (riemannXiZeroMultiplicity rho.1)

/-- Maynard--Pratt's Type-II count, with analytic multiplicity. -/
def maynardPrattTypeIIZeroCount (T sigma : ℝ) : ℕ :=
  Fintype.card (MaynardPrattTypeIIZeroIndex T sigma)

theorem maynardPrattTypeIIZeroCount_eq_sum_multiplicity
    (T sigma : ℝ) :
    maynardPrattTypeIIZeroCount T sigma =
      ∑ rho ∈ maynardPrattTypeIIZeroFinset T sigma,
        riemannXiZeroMultiplicity rho := by
  classical
  simp only [maynardPrattTypeIIZeroCount, Fintype.card_sigma,
    Fintype.card_fin]
  rw [← (maynardPrattTypeIIZeroFinset T sigma).sum_attach]
  have hattach :
      (maynardPrattTypeIIZeroFinset T sigma).attach = Finset.univ := by
    ext rho
    simp
  rw [hattach]

/-- The actual critical-line product appearing after the source change of variables. -/
def maynardPrattTypeIITwistedValue (M : ℕ) (t : ℝ) : ℂ :=
  classicalDetectorMollifier M (((1 / 2 : ℝ) : ℂ) + t * I) *
    riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)

theorem continuous_maynardPrattTypeIITwistedValue (M : ℕ) :
    Continuous (maynardPrattTypeIITwistedValue M) := by
  have hline :
      Continuous (fun t : ℝ => (((1 / 2 : ℝ) : ℂ) + t * I)) := by
    fun_prop
  have hmollifier :
      Continuous (fun t : ℝ =>
        classicalDetectorMollifier M (((1 / 2 : ℝ) : ℂ) + t * I)) :=
    (continuous_classicalDetectorMollifier M).comp hline
  have hzeta :
      Continuous (fun t : ℝ =>
        riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)) := by
    simpa only [farmerCriticalLinePoint] using continuous_riemannZeta_criticalLine
  exact hmollifier.mul hzeta

theorem rho_add_typeII_shift_eq_criticalPoint
    (rho : ℂ) (u : ℝ) :
    rho + (((1 / 2 - rho.re : ℝ) : ℂ) + u * I) =
      ((1 / 2 : ℝ) : ℂ) + (rho.im + u) * I := by
  apply Complex.ext <;> simp

/-- The Gamma argument obtained by directly parametrizing the Type-II line
`Re s = 1/2 - beta`. -/
def maynardPrattActualGammaArgument (beta u : ℝ) : ℂ :=
  ((1 / 2 - beta : ℝ) : ℂ) + u * I

/-- The positive-real-part Gamma argument displayed in the proof of Maynard--Pratt,
Lemma 24. -/
def maynardPrattDisplayedGammaArgument (beta u : ℝ) : ℂ :=
  ((beta - 1 / 2 : ℝ) : ℂ) + u * I

/-- The displayed Gamma argument is not the result of directly parametrizing the source
Type-II contour when `beta > 1/2`. -/
theorem maynardPrattActualGammaArgument_ne_displayed
    {beta : ℝ} (hbeta : 1 / 2 < beta) (u : ℝ) :
    maynardPrattActualGammaArgument beta u ≠
      maynardPrattDisplayedGammaArgument beta u := by
  intro h
  have hre := congrArg Complex.re h
  simp [maynardPrattActualGammaArgument,
    maynardPrattDisplayedGammaArgument] at hre
  linarith

/-- The one-step recurrence shifts the actual negative-real-part Gamma argument into the
positive strip. -/
theorem norm_Gamma_maynardPrattActual_recurrence
    {beta : ℝ} (hbeta : 1 / 2 < beta) (u : ℝ) :
    ‖Complex.Gamma (((3 / 2 - beta : ℝ) : ℂ) + u * I)‖ =
      ‖maynardPrattActualGammaArgument beta u‖ *
        ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ := by
  have hne : maynardPrattActualGammaArgument beta u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [maynardPrattActualGammaArgument] at hre
    linarith
  have hshift :
      maynardPrattActualGammaArgument beta u + 1 =
        (((3 / 2 - beta : ℝ) : ℂ) + u * I) := by
    apply Complex.ext
    · simp [maynardPrattActualGammaArgument]
      ring
    · simp [maynardPrattActualGammaArgument]
  rw [← hshift, Complex.Gamma_add_one _ hne, norm_mul]

/-- Exact repair of the sign mismatch: multiplying by the distance `beta - 1/2` controls the
negative-strip Gamma factor by its one-step positive-strip shift. -/
theorem sub_half_mul_norm_Gamma_maynardPrattActual_le_shifted
    {beta : ℝ} (hbeta : 1 / 2 < beta) (u : ℝ) :
    (beta - 1 / 2) *
        ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤
      ‖Complex.Gamma (((3 / 2 - beta : ℝ) : ℂ) + u * I)‖ := by
  have hnorm :
      beta - 1 / 2 ≤ ‖maynardPrattActualGammaArgument beta u‖ := by
    have hre :
        (maynardPrattActualGammaArgument beta u).re =
          1 / 2 - beta := by
      simp [maynardPrattActualGammaArgument]
    calc
      beta - 1 / 2 =
          |(maynardPrattActualGammaArgument beta u).re| := by
            rw [hre, abs_of_neg]
            · ring
            · linarith
      _ ≤ ‖maynardPrattActualGammaArgument beta u‖ :=
        Complex.abs_re_le_norm _
  calc
    (beta - 1 / 2) *
          ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤
        ‖maynardPrattActualGammaArgument beta u‖ *
          ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖Complex.Gamma (((3 / 2 - beta : ℝ) : ℂ) + u * I)‖ :=
      (norm_Gamma_maynardPrattActual_recurrence hbeta u).symm

/-- Uniform repaired bound in the nontrivial strip. The sign correction costs precisely the
factor `beta - 1/2`; after recurrence the Gamma argument has real part in `(1/2, 1)`. -/
theorem sub_half_mul_norm_Gamma_maynardPrattActual_le_two
    {beta : ℝ} (hbeta : 1 / 2 < beta) (hbeta_one : beta < 1) (u : ℝ) :
    (beta - 1 / 2) *
        ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤ 2 := by
  let z : ℂ := (((3 / 2 - beta : ℝ) : ℂ) + u * I)
  have hz_re_lower : 1 / 2 < z.re := by
    dsimp [z]
    simp
    linarith
  have hz_re_upper : z.re < 1 := by
    dsimp [z]
    simp
    linarith
  have hz_ne : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp only [zero_re] at hre
    linarith
  have hz_norm : (1 / 2 : ℝ) ≤ ‖z‖ :=
    hz_re_lower.le.trans (le_abs_self z.re) |>.trans
      (Complex.abs_re_le_norm z)
  have hshift_re_lower : 1 ≤ (z + 1).re := by
    simp only [add_re, one_re]
    linarith
  have hshift_re_upper : (z + 1).re ≤ 2 := by
    simp only [add_re, one_re]
    linarith
  have hrecurrence :
      ‖Complex.Gamma (z + 1)‖ =
        ‖z‖ * ‖Complex.Gamma z‖ := by
    rw [Complex.Gamma_add_one z hz_ne, norm_mul]
  have hhalf :
      (1 / 2 : ℝ) * ‖Complex.Gamma z‖ ≤
        ‖Complex.Gamma (z + 1)‖ := by
    rw [hrecurrence]
    exact mul_le_mul_of_nonneg_right hz_norm (norm_nonneg _)
  have htwo :
      ‖Complex.Gamma z‖ ≤
        2 * ‖Complex.Gamma (z + 1)‖ := by
    linarith [norm_nonneg (Complex.Gamma z)]
  calc
    (beta - 1 / 2) *
          ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤
        ‖Complex.Gamma z‖ := by
      simpa only [z] using
        sub_half_mul_norm_Gamma_maynardPrattActual_le_shifted hbeta u
    _ ≤ 2 * ‖Complex.Gamma (z + 1)‖ := htwo
    _ ≤ 2 * 1 := by
      gcongr
      exact Complex.Gamma.norm_le_one hshift_re_lower hshift_re_upper
    _ = 2 := by ring

/-- The source lower bound `beta - 1/2 >= 1 / log T` absorbs the recurrence loss and
recovers a uniform `2 * log T` bound for the actual negative-strip Gamma factor. -/
theorem norm_Gamma_maynardPrattActual_le_two_mul_log
    {T beta : ℝ} (hlogT : 0 < Real.log T)
    (hbeta : 1 / 2 + 1 / Real.log T ≤ beta)
    (hbeta_one : beta < 1) (u : ℝ) :
    ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤
      2 * Real.log T := by
  have hgap_pos : 0 < beta - 1 / 2 := by
    have hinv_pos : 0 < 1 / Real.log T := one_div_pos.mpr hlogT
    linarith
  have hgap_lower : 1 / Real.log T ≤ beta - 1 / 2 := by
    linarith
  have hgap_log : 1 ≤ (beta - 1 / 2) * Real.log T := by
    calc
      1 = (1 / Real.log T) * Real.log T := by
        field_simp
      _ ≤ (beta - 1 / 2) * Real.log T :=
        mul_le_mul_of_nonneg_right hgap_lower hlogT.le
  have hweighted :=
    sub_half_mul_norm_Gamma_maynardPrattActual_le_two
      (show 1 / 2 < beta by linarith) hbeta_one u
  have hquotient :
      ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤
        2 / (beta - 1 / 2) := by
    apply (le_div_iff₀ hgap_pos).2
    simpa only [mul_comm] using hweighted
  have hinv_le_log :
      1 / (beta - 1 / 2) ≤ Real.log T := by
    apply (div_le_iff₀ hgap_pos).2
    simpa only [mul_comm] using hgap_log
  calc
    ‖Complex.Gamma (maynardPrattActualGammaArgument beta u)‖ ≤
        2 / (beta - 1 / 2) := hquotient
    _ = 2 * (1 / (beta - 1 / 2)) := by ring
    _ ≤ 2 * Real.log T := by gcongr

/-- Source-range specialization for a nontrivial zero counted to the right of `sigma`. -/
theorem norm_Gamma_maynardPrattActual_le_two_mul_log_of_sourceRange
    {T sigma : ℝ} {rho : ℂ} (hT : 1 < T)
    (hsigma : 1 / 2 + 1 / Real.log T ≤ sigma)
    (hrho : IsNontrivialZero rho) (hrho_sigma : sigma ≤ rho.re) (u : ℝ) :
    ‖Complex.Gamma (maynardPrattActualGammaArgument rho.re u)‖ ≤
      2 * Real.log T := by
  apply norm_Gamma_maynardPrattActual_le_two_mul_log
      (Real.log_pos hT) (hsigma.trans hrho_sigma)
  exact nontrivial_zero_re_lt_one hrho

theorem norm_classicalDetectorMellinContourFactor_typeII_shift
    (M : ℕ) (rho : ℂ) {Y : ℝ} (hY : 0 < Y) (u : ℝ) :
    ‖classicalDetectorMellinContourFactor M rho Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ =
      Y ^ (1 / 2 - rho.re) *
        ‖Complex.Gamma (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ *
          ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖ := by
  simp only [classicalDetectorMellinContourFactor, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have hRe :
      ((((1 / 2 - rho.re : ℝ) : ℂ) + u * I)).re =
        1 / 2 - rho.re := by
    simp
  rw [hRe]
  rw [rho_add_typeII_shift_eq_criticalPoint]
  simp only [maynardPrattTypeIITwistedValue, norm_mul]
  push_cast
  ring

/-- Corrected source pointwise bound for the actual shifted Mellin integrand. The paper's
displayed positive-strip Gamma argument is replaced by recurrence plus the literal
`sigma >= 1/2 + 1 / log T` source hypothesis. -/
theorem norm_classicalDetectorMellinContourFactor_typeII_shift_le
    (M : ℕ) {T sigma Y : ℝ} {rho : ℂ}
    (hT : 1 < T) (hY : 0 < Y)
    (hsigma : 1 / 2 + 1 / Real.log T ≤ sigma)
    (hrho : IsNontrivialZero rho) (hrho_sigma : sigma ≤ rho.re) (u : ℝ) :
    ‖classicalDetectorMellinContourFactor M rho Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ ≤
      Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
        ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖ := by
  rw [norm_classicalDetectorMellinContourFactor_typeII_shift M rho hY u]
  gcongr
  exact norm_Gamma_maynardPrattActual_le_two_mul_log_of_sourceRange
    hT hsigma hrho hrho_sigma u

/-- Absolute constants for a uniform polynomial-times-exponential majorant of the actual
Type-II shifted integrand. This keeps the critical-line zeta exponent and all source-parameter
dependence explicit. -/
theorem exists_norm_classicalDetectorMellinContourFactor_typeII_shift_le_exp :
    ∃ C p : ℝ, 0 < C ∧ 0 < p ∧
      ∀ (M : ℕ) {rho : ℂ}, IsNontrivialZero rho →
        ∀ {Y : ℝ}, 0 < Y → ∀ u : ℝ, 1 ≤ |u| →
          ‖classicalDetectorMellinContourFactor M rho Y
              (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ ≤
            C * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
              (1 + |rho.im|) ^ (3 / 8 : ℝ) *
              (|u| + 2) ^ p *
              Real.exp (-(Real.pi / 2) * |u|) := by
  obtain ⟨q, hq, hgamma⟩ :=
    exists_norm_Gamma_classicalDetectorStrip_le
  obtain ⟨A, hA, hzeta⟩ :=
    exists_norm_riemannZeta_criticalLine_le_rpow_all
  refine ⟨3 * A, q + 3 / 8, mul_pos (by norm_num) hA,
    add_pos_of_pos_of_nonneg hq (by norm_num), ?_⟩
  intro M rho hrho Y hY u hu
  have hx :
      1 / 2 - rho.re ∈ Set.Icc (1 / 2 - rho.re) 2 := by
    exact ⟨le_rfl, by linarith [nontrivial_zero_re_pos hrho]⟩
  have hgamma' :=
    hgamma hrho (1 / 2 - rho.re) u hx hu
  have hmollifier :
      ‖classicalDetectorMollifier M
          (((1 / 2 : ℝ) : ℂ) + ((rho.im + u : ℝ) : ℂ) * I)‖ ≤
        (M : ℝ) := by
    apply norm_classicalDetectorMollifier_le_nat
    norm_num
  have hbase :
      1 + |rho.im + u| ≤ (1 + |rho.im|) * (|u| + 2) := by
    have hadd := abs_add_le rho.im u
    nlinarith [abs_nonneg rho.im, abs_nonneg u]
  have hzeta' :
      ‖riemannZeta
          (((1 / 2 : ℝ) : ℂ) + ((rho.im + u : ℝ) : ℂ) * I)‖ ≤
        A * ((1 + |rho.im|) ^ (3 / 8 : ℝ) *
          (|u| + 2) ^ (3 / 8 : ℝ)) := by
    calc
      ‖riemannZeta
          (((1 / 2 : ℝ) : ℂ) + ((rho.im + u : ℝ) : ℂ) * I)‖ =
          ‖riemannZeta
            ((1 / 2 : ℂ) + ((rho.im + u : ℝ) : ℂ) * I)‖ := by
        norm_num
      _ ≤
          A * (1 + |rho.im + u|) ^ (3 / 8 : ℝ) :=
        hzeta (rho.im + u)
      _ ≤ A * ((1 + |rho.im|) * (|u| + 2)) ^
          (3 / 8 : ℝ) := by
        gcongr
      _ = A * ((1 + |rho.im|) ^ (3 / 8 : ℝ) *
          (|u| + 2) ^ (3 / 8 : ℝ)) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
  have htwisted :
      ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖ ≤
        (M : ℝ) *
          (A * ((1 + |rho.im|) ^ (3 / 8 : ℝ) *
            (|u| + 2) ^ (3 / 8 : ℝ))) := by
    rw [maynardPrattTypeIITwistedValue, norm_mul]
    exact mul_le_mul hmollifier hzeta'
      (norm_nonneg _)
      (Nat.cast_nonneg M)
  rw [norm_classicalDetectorMellinContourFactor_typeII_shift M rho hY u]
  calc
    Y ^ (1 / 2 - rho.re) *
          ‖Complex.Gamma
            (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ *
          ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖ ≤
        Y ^ (1 / 2 - rho.re) *
          (3 * (|u| + 2) ^ q *
            Real.exp (-(Real.pi / 2) * |u|)) *
          ((M : ℝ) *
            (A * ((1 + |rho.im|) ^ (3 / 8 : ℝ) *
              (|u| + 2) ^ (3 / 8 : ℝ)))) := by
      gcongr
    _ = (3 * A) * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
          (1 + |rho.im|) ^ (3 / 8 : ℝ) *
          (|u| + 2) ^ (q + 3 / 8) *
          Real.exp (-(Real.pi / 2) * |u|) := by
      rw [Real.rpow_add (by positivity : 0 < |u| + 2)]
      ring

/-- Beyond one absolute radius, half of the Gamma exponential absorbs the fixed polynomial
factor in the uniform Type-II majorant. -/
theorem exists_add_two_rpow_mul_exp_pi_div_two_le_exp_pi_div_four
    (p : ℝ) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ v : ℝ, R0 ≤ v →
      (v + 2) ^ p * Real.exp (-(Real.pi / 2) * v) ≤
        Real.exp (-(Real.pi / 4) * v) := by
  have hpi_four : 0 < Real.pi / 4 := div_pos Real.pi_pos (by norm_num)
  have hlimit :=
    tendsto_add_two_rpow_mul_exp_neg_mul_atTop_nhds_zero
      p (Real.pi / 4) hpi_four
  rw [Metric.tendsto_atTop] at hlimit
  obtain ⟨R0, hR0⟩ := hlimit 1 zero_lt_one
  refine ⟨max 1 R0, le_max_left _ _, ?_⟩
  intro v hv
  have hv_one : 1 ≤ v := (le_max_left 1 R0).trans hv
  have hv_R0 : R0 ≤ v := (le_max_right 1 R0).trans hv
  have hsmall := hR0 v hv_R0
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg] at hsmall
  · have hexp :
        Real.exp (-(Real.pi / 2) * v) =
          Real.exp (-(Real.pi / 4) * v) *
            Real.exp (-(Real.pi / 4) * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp, ← mul_assoc]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hsmall.le
        (Real.exp_nonneg (-(Real.pi / 4) * v))
  · exact mul_nonneg
      (Real.rpow_nonneg (by linarith) p)
      (Real.exp_nonneg _)

/-- The actual Type-II shifted integrand has a pure exponential tail after one absolute
radius. All dependence on the source parameters remains in the displayed prefactor. -/
theorem exists_norm_classicalDetectorMellinContourFactor_typeII_shift_le_pureExp :
    ∃ C R0 : ℝ, 0 < C ∧ 1 ≤ R0 ∧
      ∀ (M : ℕ) {rho : ℂ}, IsNontrivialZero rho →
        ∀ {Y : ℝ}, 0 < Y → ∀ u : ℝ, R0 ≤ |u| →
          ‖classicalDetectorMellinContourFactor M rho Y
              (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ ≤
            C * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
              (1 + |rho.im|) ^ (3 / 8 : ℝ) *
              Real.exp (-(Real.pi / 4) * |u|) := by
  obtain ⟨C, p, hC, hp, hraw⟩ :=
    exists_norm_classicalDetectorMellinContourFactor_typeII_shift_le_exp
  obtain ⟨R0, hR0, habsorb⟩ :=
    exists_add_two_rpow_mul_exp_pi_div_two_le_exp_pi_div_four p
  refine ⟨C, R0, hC, hR0, ?_⟩
  intro M rho hrho Y hY u hu
  let K : ℝ :=
    C * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
      (1 + |rho.im|) ^ (3 / 8 : ℝ)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hmajor := hraw M hrho hY u (hR0.trans hu)
  calc
    ‖classicalDetectorMellinContourFactor M rho Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ ≤
        K * ((|u| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |u|)) := by
      simpa only [K, mul_assoc] using hmajor
    _ ≤ K * Real.exp (-(Real.pi / 4) * |u|) :=
      mul_le_mul_of_nonneg_left (habsorb |u| hu) hK
    _ = C * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
          (1 + |rho.im|) ^ (3 / 8 : ℝ) *
          Real.exp (-(Real.pi / 4) * |u|) := rfl

/-- The full shifted-line norm mass before the source Gamma factor is separated. -/
def maynardPrattTypeIIContourNormMass
    (M : ℕ) (rho : ℂ) (Y : ℝ) : ℝ :=
  ∫ u : ℝ,
    ‖classicalDetectorMellinContourFactor M rho Y
      (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖

/-- The actual shifted-line norm mass on a symmetric truncation window. -/
def maynardPrattTypeIIContourNormMassOn
    (M : ℕ) (rho : ℂ) (Y R : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Icc (-R) R,
    ‖classicalDetectorMellinContourFactor M rho Y
      (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖

/-- The norm mass discarded outside a symmetric Type-II contour window. -/
def maynardPrattTypeIIContourNormTailMass
    (M : ℕ) (rho : ℂ) (Y R : ℝ) : ℝ :=
  ∫ u : ℝ in (Set.Icc (-R) R)ᶜ,
    ‖classicalDetectorMellinContourFactor M rho Y
      (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖

theorem integrable_norm_classicalDetectorMellinContourFactor_typeII_shift
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun u : ℝ =>
      ‖classicalDetectorMellinContourFactor M rho Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖) := by
  simpa only using
    (integrable_classicalDetectorMellinContourFactor_left
      M hrho hbeta hY).norm

theorem maynardPrattTypeIIContourNormMass_eq_on_add_tail
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) (R : ℝ) :
    maynardPrattTypeIIContourNormMass M rho Y =
      maynardPrattTypeIIContourNormMassOn M rho Y R +
        maynardPrattTypeIIContourNormTailMass M rho Y R := by
  exact (integral_add_compl measurableSet_Icc
    (integrable_norm_classicalDetectorMellinContourFactor_typeII_shift
      M hrho hbeta hY)).symm

/-- Uniform integral tail bound for the actual Type-II shifted line. The absolute constants
are independent of `M`, `rho`, and `Y`. -/
theorem exists_maynardPrattTypeIIContourNormTailMass_le :
    ∃ D R0 : ℝ, 0 < D ∧ 1 ≤ R0 ∧
      ∀ (M : ℕ) {rho : ℂ}, IsNontrivialZero rho →
        1 / 2 < rho.re → ∀ {Y : ℝ}, 0 < Y →
          ∀ R : ℝ, R0 ≤ R →
            maynardPrattTypeIIContourNormTailMass M rho Y R ≤
              D * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
                (1 + |rho.im|) ^ (3 / 8 : ℝ) *
                Real.exp (-(Real.pi / 4) * R) := by
  obtain ⟨C, R0, hC, hR0, hpure⟩ :=
    exists_norm_classicalDetectorMellinContourFactor_typeII_shift_le_pureExp
  let a : ℝ := Real.pi / 4
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  refine ⟨8 * C / Real.pi, R0,
    div_pos (mul_pos (by norm_num) hC) Real.pi_pos, hR0, ?_⟩
  intro M rho hrho hbeta Y hY R hR
  let f : ℝ → ℝ := fun u =>
    ‖classicalDetectorMellinContourFactor M rho Y
      (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖
  let K : ℝ :=
    C * (M : ℝ) * Y ^ (1 / 2 - rho.re) *
      (1 + |rho.im|) ^ (3 / 8 : ℝ)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hR_one : 1 ≤ R := hR0.trans hR
  have hminusR : -R ≤ R := by linarith
  have hf : Integrable f :=
    integrable_norm_classicalDetectorMellinContourFactor_typeII_shift
      M hrho hbeta hY
  have hleft : IntegrableOn f (Set.Iio (-R)) := hf.integrableOn
  have hright : IntegrableOn f (Set.Ioi R) := hf.integrableOn
  have hleftMajor :
      IntegrableOn (fun u : ℝ => K * Real.exp (a * u))
        (Set.Iio (-R)) := by
    apply Integrable.const_mul
    exact (integrableOn_exp_mul_Iic ha (-R)).mono_set
      (Set.Iio_subset_Iic le_rfl)
  have hrightMajor :
      IntegrableOn (fun u : ℝ => K * Real.exp (-a * u))
        (Set.Ioi R) := by
    exact (integrableOn_exp_mul_Ioi (by linarith : -a < 0) R).const_mul K
  have hleftBound :
      (∫ u : ℝ in Set.Iio (-R), f u) ≤
        K * (Real.exp (-a * R) / a) := by
    calc
      (∫ u : ℝ in Set.Iio (-R), f u) ≤
          ∫ u : ℝ in Set.Iio (-R), K * Real.exp (a * u) := by
        apply setIntegral_mono_on hleft hleftMajor measurableSet_Iio
        intro u hu
        change u < -R at hu
        have hu_neg : u < 0 := hu.trans_le (by linarith)
        have hu_abs : |u| = -u := abs_of_neg hu_neg
        have hu_radius : R0 ≤ |u| := by
          rw [hu_abs]
          linarith
        have hpoint := hpure M hrho hY u hu_radius
        rw [hu_abs] at hpoint
        change f u ≤ K * Real.exp (-(Real.pi / 4) * -u) at hpoint
        rw [show -(Real.pi / 4) * -u = a * u by
          dsimp only [a]
          ring] at hpoint
        exact hpoint
      _ = K * (Real.exp (-a * R) / a) := by
        rw [← integral_Iic_eq_integral_Iio, MeasureTheory.integral_const_mul,
          integral_exp_mul_Iic ha]
        congr 2
        congr 1
        ring
  have hrightBound :
      (∫ u : ℝ in Set.Ioi R, f u) ≤
        K * (Real.exp (-a * R) / a) := by
    calc
      (∫ u : ℝ in Set.Ioi R, f u) ≤
          ∫ u : ℝ in Set.Ioi R, K * Real.exp (-a * u) := by
        apply setIntegral_mono_on hright hrightMajor measurableSet_Ioi
        intro u hu
        have hu_pos : 0 < u := (by linarith : 0 < R).trans hu
        have hu_abs : |u| = u := abs_of_pos hu_pos
        have hu_radius : R0 ≤ |u| := by
          rw [hu_abs]
          exact hR.trans hu.le
        have hpoint := hpure M hrho hY u hu_radius
        rw [hu_abs] at hpoint
        simpa only [f, K, a] using hpoint
      _ = K * (Real.exp (-a * R) / a) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Ioi (by linarith : -a < 0)]
        field_simp
  have hcompl :
      (Set.Icc (-R) R)ᶜ = Set.Iio (-R) ∪ Set.Ioi R := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi, not_and_or, not_le]
  have hdisjoint :
      Disjoint (Set.Iio (-R)) (Set.Ioi R) :=
    (Set.Ioi_disjoint_Iio_of_le hminusR).symm
  have hunion :
      (∫ u : ℝ in Set.Iio (-R) ∪ Set.Ioi R, f u) =
        (∫ u : ℝ in Set.Iio (-R), f u) +
          ∫ u : ℝ in Set.Ioi R, f u :=
    setIntegral_union hdisjoint measurableSet_Ioi hleft hright
  calc
    maynardPrattTypeIIContourNormTailMass M rho Y R =
        (∫ u : ℝ in Set.Iio (-R), f u) +
          ∫ u : ℝ in Set.Ioi R, f u := by
      rw [maynardPrattTypeIIContourNormTailMass, hcompl, hunion]
    _ ≤ K * (Real.exp (-a * R) / a) +
          K * (Real.exp (-a * R) / a) :=
      add_le_add hleftBound hrightBound
    _ = (8 * C / Real.pi) * (M : ℝ) *
          Y ^ (1 / 2 - rho.re) *
          (1 + |rho.im|) ^ (3 / 8 : ℝ) *
          Real.exp (-(Real.pi / 4) * R) := by
      dsimp only [K, a]
      field_simp [Real.pi_ne_zero]
      ring

/-- At the literal source scales and source window `(log T)^2`, the corrected Gamma tail is
eventually at most one, uniformly over zeros in the dyadic height range. -/
theorem eventually_maynardPrattTypeIIContourNormTailMass_source_le_one :
    ∀ᶠ T : ℝ in atTop,
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        1 / 2 < rho.re → T ≤ rho.im → rho.im ≤ 2 * T →
          maynardPrattTypeIIContourNormTailMass
              (classicalDetectorSourceM T) rho
              (classicalDetectorSourceY T) (Real.log T ^ (2 : ℕ)) ≤ 1 := by
  obtain ⟨D, R0, hD, hR0, htail⟩ :=
    exists_maynardPrattTypeIIContourNormTailMass_le
  let B : ℝ := 2 * D * 3 ^ (3 / 8 : ℝ)
  have hdecay :
      Tendsto (fun T : ℝ => B * T ^ (-(1 / 2 : ℝ)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))))
  have hsmall :
      ∀ᶠ T : ℝ in atTop, B * T ^ (-(1 / 2 : ℝ)) < 1 :=
    (tendsto_order.1 hdecay).2 1 zero_lt_one
  filter_upwards [eventually_classicalDetectorSourceParameters, hsmall,
    eventually_ge_atTop (Real.exp (max R0 2))] with T hparameters hsmallT hTlarge
  rcases hparameters with
    ⟨hYLower, hYUpper, hMOne, hMK, hMUpper, hKUpper, hscaleLower⟩
  intro rho hrho hbeta himLower himUpper
  have hTpos : 0 < T :=
    (Real.exp_pos (max R0 2)).trans_le hTlarge
  have hTOne : 1 ≤ T := by
    have hmax_nonneg : 0 ≤ max R0 2 :=
      zero_le_two.trans (le_max_right R0 2)
    exact (Real.one_le_exp hmax_nonneg).trans hTlarge
  have hlogLower : max R0 2 ≤ Real.log T := by
    calc
      max R0 2 = Real.log (Real.exp (max R0 2)) := by
        rw [Real.log_exp]
      _ ≤ Real.log T :=
        Real.log_le_log (Real.exp_pos _) hTlarge
  have hlogR0 : R0 ≤ Real.log T :=
    (le_max_left R0 2).trans hlogLower
  have hlogTwo : 2 ≤ Real.log T :=
    (le_max_right R0 2).trans hlogLower
  have hwindow : R0 ≤ Real.log T ^ (2 : ℕ) := by
    have hlog_le_sq :
        Real.log T ≤ Real.log T ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (Real.log T)]
    exact hlogR0.trans hlog_le_sq
  have hsourceYPos : 0 < classicalDetectorSourceY T := by
    linarith
  have hsourceYOne : 1 ≤ classicalDetectorSourceY T := by
    linarith
  have hYpower :
      classicalDetectorSourceY T ^ (1 / 2 - rho.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hsourceYOne (by linarith)
  have hMpower :
      T ^ (1 / 100 : ℝ) ≤ T ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hTOne (by norm_num)
  have hMUpper' :
      (classicalDetectorSourceM T : ℝ) ≤
        2 * T ^ (1 / 8 : ℝ) :=
    hMUpper.trans (mul_le_mul_of_nonneg_left hMpower (by norm_num))
  have himPos : 0 < rho.im := hTpos.trans_le himLower
  have himBase :
      1 + |rho.im| ≤ 3 * T := by
    rw [abs_of_pos himPos]
    linarith
  have himPower :
      (1 + |rho.im|) ^ (3 / 8 : ℝ) ≤
        3 ^ (3 / 8 : ℝ) * T ^ (3 / 8 : ℝ) := by
    calc
      (1 + |rho.im|) ^ (3 / 8 : ℝ) ≤
          (3 * T) ^ (3 / 8 : ℝ) := by
        exact Real.rpow_le_rpow (by positivity) himBase (by norm_num)
      _ = 3 ^ (3 / 8 : ℝ) * T ^ (3 / 8 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hTpos.le]
  have hpiLog :
      1 ≤ (Real.pi / 4) * Real.log T := by
    calc
      (1 : ℝ) ≤ (3 / 4 : ℝ) * 2 := by norm_num
      _ ≤ (Real.pi / 4) * Real.log T := by
        exact mul_le_mul
          (by linarith [Real.pi_gt_three])
          hlogTwo (by norm_num) (by linarith [Real.pi_gt_three])
  have hlogNonneg : 0 ≤ Real.log T := by linarith
  have hquad :
      Real.log T ≤ (Real.pi / 4) * Real.log T ^ (2 : ℕ) := by
    calc
      Real.log T = 1 * Real.log T := by ring
      _ ≤ ((Real.pi / 4) * Real.log T) * Real.log T :=
        mul_le_mul_of_nonneg_right hpiLog hlogNonneg
      _ = (Real.pi / 4) * Real.log T ^ (2 : ℕ) := by ring
  have hexpDecay :
      Real.exp (-(Real.pi / 4) * Real.log T ^ (2 : ℕ)) ≤ T⁻¹ := by
    calc
      Real.exp (-(Real.pi / 4) * Real.log T ^ (2 : ℕ)) ≤
          Real.exp (-Real.log T) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = T⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hTpos]
  have hpowerCombine :
      T ^ (1 / 8 : ℝ) * T ^ (3 / 8 : ℝ) * T⁻¹ =
        T ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one T, ← Real.rpow_add hTpos,
      ← Real.rpow_add hTpos]
    norm_num
  have hraw :=
    htail (classicalDetectorSourceM T) hrho hbeta hsourceYPos
      (Real.log T ^ (2 : ℕ)) hwindow
  calc
    maynardPrattTypeIIContourNormTailMass
        (classicalDetectorSourceM T) rho
        (classicalDetectorSourceY T) (Real.log T ^ (2 : ℕ)) ≤
        D * (classicalDetectorSourceM T : ℝ) *
          classicalDetectorSourceY T ^ (1 / 2 - rho.re) *
          (1 + |rho.im|) ^ (3 / 8 : ℝ) *
          Real.exp (-(Real.pi / 4) * Real.log T ^ (2 : ℕ)) := hraw
    _ ≤ D * (2 * T ^ (1 / 8 : ℝ)) * 1 *
          (3 ^ (3 / 8 : ℝ) * T ^ (3 / 8 : ℝ)) * T⁻¹ := by
      gcongr
    _ = B * (T ^ (1 / 8 : ℝ) * T ^ (3 / 8 : ℝ) * T⁻¹) := by
      dsimp only [B]
      ring
    _ = B * T ^ (-(1 / 2 : ℝ)) := by rw [hpowerCombine]
    _ ≤ 1 := hsmallT.le

theorem norm_inv_two_pi_le_one_sixth :
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ≤ 1 / 6 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos zero_lt_one (mul_pos (by norm_num) Real.pi_pos))]
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).2
  nlinarith [Real.pi_gt_three]

/-- Every fixed actual Type-II shifted line is exhausted by symmetric compact windows. This
is qualitative truncation; it is not uniform in `T` or `rho`. -/
theorem tendsto_maynardPrattTypeIIContourNormMassOn_nat
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    Tendsto
      (fun N : ℕ =>
        maynardPrattTypeIIContourNormMassOn M rho Y N)
      atTop
      (𝓝 (maynardPrattTypeIIContourNormMass M rho Y)) := by
  let f : ℝ → ℝ := fun u =>
    ‖classicalDetectorMellinContourFactor M rho Y
      (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖
  let s : ℕ → Set ℝ := fun N => Set.Icc (-(N : ℝ)) N
  have hs_measurable : ∀ N, MeasurableSet (s N) := by
    intro N
    exact measurableSet_Icc
  have hs_mono : Monotone s := by
    intro N K hNK u hu
    have hNKreal : (N : ℝ) ≤ K := by exact_mod_cast hNK
    exact ⟨(neg_le_neg hNKreal).trans hu.1, hu.2.trans hNKreal⟩
  have hs_union : (⋃ N, s N) = Set.univ := by
    ext u
    constructor
    · intro
      trivial
    · intro
      obtain ⟨N, hN⟩ := exists_nat_gt |u|
      apply Set.mem_iUnion.mpr
      refine ⟨N, ?_⟩
      have hNreal : |u| ≤ (N : ℝ) := le_of_lt hN
      constructor
      · exact (neg_le_neg hNreal).trans (neg_abs_le u)
      · exact (le_abs_self u).trans hNreal
  have hf : Integrable f :=
    integrable_norm_classicalDetectorMellinContourFactor_typeII_shift
      M hrho hbeta hY
  have hlimit :=
    tendsto_setIntegral_of_monotone hs_measurable hs_mono
      (hf.integrableOn : IntegrableOn f (⋃ N, s N))
  rw [hs_union] at hlimit
  simpa only [f, s, maynardPrattTypeIIContourNormMassOn,
    maynardPrattTypeIIContourNormMass, setIntegral_univ] using hlimit

/-- Qualitative fixed-parameter truncation consequence. The radius supplied here is not the
source radius `(log T)^2` and carries no uniformity. -/
theorem exists_maynardPrattTypeIIContourNormMassOn_add_pos
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y epsilon : ℝ}
    (hY : 0 < Y) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ,
      maynardPrattTypeIIContourNormMass M rho Y <
        maynardPrattTypeIIContourNormMassOn M rho Y N + epsilon := by
  have hlimit :=
    tendsto_maynardPrattTypeIIContourNormMassOn_nat
      M hrho hbeta hY
  rw [Metric.tendsto_atTop] at hlimit
  obtain ⟨N, hN⟩ := hlimit epsilon hepsilon
  refine ⟨N, ?_⟩
  have hdist := hN N le_rfl
  rw [Real.dist_eq] at hdist
  have hlow := (abs_lt.mp hdist).1
  linarith

/-- On the source compact window, the corrected Gamma estimate reduces the actual contour
mass to the unweighted critical-line mollifier--zeta `L1` mass. -/
theorem maynardPrattTypeIIContourNormMassOn_le_twistedNorm
    (M : ℕ) {T sigma Y R : ℝ} {rho : ℂ}
    (hT : 1 < T) (hY : 0 < Y)
    (hsigma : 1 / 2 + 1 / Real.log T ≤ sigma)
    (hrho : IsNontrivialZero rho) (hrho_sigma : sigma ≤ rho.re) :
    maynardPrattTypeIIContourNormMassOn M rho Y R ≤
      Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
        (∫ u : ℝ in Set.Icc (-R) R,
          ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖) := by
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hbeta : 1 / 2 < rho.re := by
    have hinv : 0 < 1 / Real.log T := one_div_pos.mpr hlogT
    linarith
  have hleft :
      IntegrableOn
        (fun u : ℝ =>
          ‖classicalDetectorMellinContourFactor M rho Y
            (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖)
        (Set.Icc (-R) R) :=
    (integrable_norm_classicalDetectorMellinContourFactor_typeII_shift
      M hrho hbeta hY).integrableOn
  have htwisted :
      IntegrableOn
        (fun u : ℝ =>
          ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖)
        (Set.Icc (-R) R) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact ((continuous_maynardPrattTypeIITwistedValue M).comp
      (by fun_prop)).norm.continuousOn
  have hright :
      IntegrableOn
        (fun u : ℝ =>
          (Y ^ (1 / 2 - rho.re) * (2 * Real.log T)) *
            ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖)
        (Set.Icc (-R) R) :=
    htwisted.const_mul _
  calc
    maynardPrattTypeIIContourNormMassOn M rho Y R =
        ∫ u : ℝ in Set.Icc (-R) R,
          ‖classicalDetectorMellinContourFactor M rho Y
            (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ := rfl
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R,
          (Y ^ (1 / 2 - rho.re) * (2 * Real.log T)) *
            ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖ := by
      apply setIntegral_mono_on hleft hright measurableSet_Icc
      intro u _
      exact norm_classicalDetectorMellinContourFactor_typeII_shift_le
        M hT hY hsigma hrho hrho_sigma u
    _ = Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
          (∫ u : ℝ in Set.Icc (-R) R,
            ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖) := by
      rw [MeasureTheory.integral_const_mul]

/-- The full critical-line mass after the source change of variables. -/
def maynardPrattTypeIICriticalNormMass
    (M : ℕ) (rho : ℂ) : ℝ :=
  ∫ u : ℝ,
    ‖Complex.Gamma (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ *
      ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖

theorem maynardPrattTypeIIContourNormMass_eq
    (M : ℕ) (rho : ℂ) {Y : ℝ} (hY : 0 < Y) :
    maynardPrattTypeIIContourNormMass M rho Y =
      Y ^ (1 / 2 - rho.re) *
        maynardPrattTypeIICriticalNormMass M rho := by
  simp only [maynardPrattTypeIIContourNormMass,
    maynardPrattTypeIICriticalNormMass,
    norm_classicalDetectorMellinContourFactor_typeII_shift M rho hY]
  simp_rw [mul_assoc]
  rw [MeasureTheory.integral_const_mul]

/-- Type-II largeness already charges the full shifted-line norm mass. No tail truncation or
fourth-moment estimate is used here. -/
theorem one_third_le_normScale_mul_typeIIContourNormMass
    {M : ℕ} {rho : ℂ} {Y : ℝ}
    (hII : ClassicalDetectorTypeII M Y rho) :
    (1 / 3 : ℝ) ≤
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        maynardPrattTypeIIContourNormMass M rho Y := by
  unfold ClassicalDetectorTypeII at hII
  rw [classicalDetectorMellinLineIntegral] at hII
  calc
    (1 / 3 : ℝ) ≤
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ u : ℝ,
            classicalDetectorMellinContourFactor M rho Y
              (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ := hII
    _ = ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        ‖∫ u : ℝ,
          classicalDetectorMellinContourFactor M rho Y
            (((1 / 2 - rho.re : ℝ) : ℂ) + u * I)‖ := norm_mul _ _
    _ ≤ ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        maynardPrattTypeIIContourNormMass M rho Y := by
      gcongr
      exact norm_integral_le_integral_norm _

/-- If a named truncation error consumes at most half of the Type-II threshold, the actual
compact-window contour mass retains the other half. -/
theorem one_sixth_le_normScale_mul_typeIIContourNormMassOn
    {M : ℕ} {rho : ℂ} {Y R delta : ℝ}
    (hII : ClassicalDetectorTypeII M Y rho)
    (htrunc :
      maynardPrattTypeIIContourNormMass M rho Y ≤
        maynardPrattTypeIIContourNormMassOn M rho Y R + delta)
    (hdelta :
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ * delta ≤ 1 / 6) :
    (1 / 6 : ℝ) ≤
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        maynardPrattTypeIIContourNormMassOn M rho Y R := by
  have hscale_nonneg :
      0 ≤ ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ := norm_nonneg _
  have htrunc_scaled :=
    mul_le_mul_of_nonneg_left htrunc hscale_nonneg
  rw [mul_add] at htrunc_scaled
  have hfull := one_third_le_normScale_mul_typeIIContourNormMass hII
  linarith

/-- Corrected compact-window `L1` charge. The only unproved analytic input exposed here is the
explicit truncation inequality and its threshold budget. -/
theorem one_sixth_le_normScale_mul_rpow_mul_log_mul_typeIITwistedNormOn
    {M : ℕ} {T sigma Y R delta : ℝ} {rho : ℂ}
    (hT : 1 < T) (hY : 0 < Y)
    (hsigma : 1 / 2 + 1 / Real.log T ≤ sigma)
    (hrho : IsNontrivialZero rho) (hrho_sigma : sigma ≤ rho.re)
    (hII : ClassicalDetectorTypeII M Y rho)
    (htrunc :
      maynardPrattTypeIIContourNormMass M rho Y ≤
        maynardPrattTypeIIContourNormMassOn M rho Y R + delta)
    (hdelta :
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ * delta ≤ 1 / 6) :
    (1 / 6 : ℝ) ≤
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        (Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
          (∫ u : ℝ in Set.Icc (-R) R,
            ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖)) := by
  calc
    (1 / 6 : ℝ) ≤
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
          maynardPrattTypeIIContourNormMassOn M rho Y R :=
      one_sixth_le_normScale_mul_typeIIContourNormMassOn
        hII htrunc hdelta
    _ ≤ ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
          (Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
            (∫ u : ℝ in Set.Icc (-R) R,
              ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖)) := by
      gcongr
      exact maynardPrattTypeIIContourNormMassOn_le_twistedNorm
        M hT hY hsigma hrho hrho_sigma

/-- Exact source-line reduction from the compiled Type-II predicate to full critical-line
mollifier--zeta mass. Gamma truncation and Holder's fourth-power step remain separate. -/
theorem one_third_le_normScale_mul_rpow_mul_typeIICriticalNormMass
    {M : ℕ} {rho : ℂ} {Y : ℝ} (hY : 0 < Y)
    (hII : ClassicalDetectorTypeII M Y rho) :
    (1 / 3 : ℝ) ≤
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        (Y ^ (1 / 2 - rho.re) *
          maynardPrattTypeIICriticalNormMass M rho) := by
  rw [← maynardPrattTypeIIContourNormMass_eq M rho hY]
  exact one_third_le_normScale_mul_typeIIContourNormMass hII

/-- The exact `L1`--`L4` Holder step used after the source truncates the Gamma integral. -/
theorem integral_norm_le_measure_rpow_mul_integral_norm_rpow_four
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    (f : α → E) (hf : MemLp f (ENNReal.ofReal 4) μ) :
    (∫ x, ‖f x‖ ∂μ) ≤
      (μ.real Set.univ) ^ (3 / 4 : ℝ) *
        (∫ x, ‖f x‖ ^ (4 : ℝ) ∂μ) ^ (1 / 4 : ℝ) := by
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h :=
    integral_mul_norm_le_Lp_mul_Lq hpq
      (memLp_const (1 : ℝ) :
        MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (4 / 3 : ℝ)) μ)
      hf.norm
  simp only [norm_one, one_mul, Real.one_rpow, integral_const, smul_eq_mul,
    mul_one, Real.norm_of_nonneg (norm_nonneg _)] at h
  convert h using 1
  all_goals norm_num

/-- The actual unweighted local fourth moment centered at the ordinate of `rho`. -/
def maynardPrattTypeIILocalFourthMoment
    (M : ℕ) (rho : ℂ) (R : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Icc (-R) R,
    ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖ ^ (4 : ℝ)

theorem typeIIWindow_measureReal (R : ℝ) (hR : 0 ≤ R) :
    (volume.restrict (Set.Icc (-R) R)).real Set.univ = 2 * R := by
  rw [measureReal_restrict_apply_univ]
  simp [Measure.real, Real.volume_Icc, hR]
  ring

/-- Continuity on the compact source window supplies the finite local `L4` membership required
by Holder; no zeta moment estimate is used. -/
theorem maynardPrattTypeIITwistedValue_memLp_four_restrict
    (M : ℕ) (rho : ℂ) (R : ℝ) :
    MemLp
      (fun u : ℝ => maynardPrattTypeIITwistedValue M (rho.im + u))
      (ENNReal.ofReal 4) (volume.restrict (Set.Icc (-R) R)) := by
  let f : ℝ → ℂ := fun u =>
    maynardPrattTypeIITwistedValue M (rho.im + u)
  have hf : Continuous f :=
    (continuous_maynardPrattTypeIITwistedValue M).comp (by fun_prop)
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact hC ⟨u, hu, rfl⟩

/-- Holder on the literal symmetric source window. The remaining analytic task before using
this theorem is to dominate the truncated Gamma factor uniformly. -/
theorem integral_typeIITwistedNorm_restrict_le
    (M : ℕ) (rho : ℂ) (R : ℝ)
    (hmem :
      MemLp
        (fun u : ℝ => maynardPrattTypeIITwistedValue M (rho.im + u))
        (ENNReal.ofReal 4) (volume.restrict (Set.Icc (-R) R))) :
    (∫ u : ℝ in Set.Icc (-R) R,
        ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖) ≤
      ((volume.restrict (Set.Icc (-R) R)).real Set.univ) ^ (3 / 4 : ℝ) *
        (maynardPrattTypeIILocalFourthMoment M rho R) ^ (1 / 4 : ℝ) := by
  simpa only [maynardPrattTypeIILocalFourthMoment] using
    integral_norm_le_measure_rpow_mul_integral_norm_rpow_four
      (fun u : ℝ => maynardPrattTypeIITwistedValue M (rho.im + u)) hmem

/-- Unconditional local Holder step for the actual source mollifier--zeta product. -/
theorem integral_typeIITwistedNorm_restrict_le_localFourthMoment
    (M : ℕ) (rho : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ u : ℝ in Set.Icc (-R) R,
        ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖) ≤
      (2 * R) ^ (3 / 4 : ℝ) *
        (maynardPrattTypeIILocalFourthMoment M rho R) ^ (1 / 4 : ℝ) :=
  by
    rw [← typeIIWindow_measureReal R hR]
    exact integral_typeIITwistedNorm_restrict_le M rho R
      (maynardPrattTypeIITwistedValue_memLp_four_restrict M rho R)

/-- The corrected local fourth-moment charge following the explicit truncation premise.
No packing theorem or global twisted fourth-moment upper bound is used. -/
theorem one_sixth_le_normScale_mul_rpow_mul_log_mul_typeIILocalFourthMoment
    {M : ℕ} {T sigma Y R delta : ℝ} {rho : ℂ}
    (hT : 1 < T) (hY : 0 < Y) (hR : 0 ≤ R)
    (hsigma : 1 / 2 + 1 / Real.log T ≤ sigma)
    (hrho : IsNontrivialZero rho) (hrho_sigma : sigma ≤ rho.re)
    (hII : ClassicalDetectorTypeII M Y rho)
    (htrunc :
      maynardPrattTypeIIContourNormMass M rho Y ≤
        maynardPrattTypeIIContourNormMassOn M rho Y R + delta)
    (hdelta :
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ * delta ≤ 1 / 6) :
    (1 / 6 : ℝ) ≤
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
        (Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
          ((2 * R) ^ (3 / 4 : ℝ) *
            (maynardPrattTypeIILocalFourthMoment M rho R) ^
              (1 / 4 : ℝ))) := by
  calc
    (1 / 6 : ℝ) ≤
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
          (Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
            (∫ u : ℝ in Set.Icc (-R) R,
              ‖maynardPrattTypeIITwistedValue M (rho.im + u)‖)) :=
      one_sixth_le_normScale_mul_rpow_mul_log_mul_typeIITwistedNormOn
        hT hY hsigma hrho hrho_sigma hII htrunc hdelta
    _ ≤ ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
          (Y ^ (1 / 2 - rho.re) * (2 * Real.log T) *
            ((2 * R) ^ (3 / 4 : ℝ) *
              (maynardPrattTypeIILocalFourthMoment M rho R) ^
                (1 / 4 : ℝ))) := by
      have hcoefficient :
          0 ≤ Y ^ (1 / 2 - rho.re) * (2 * Real.log T) := by
        exact mul_nonneg (Real.rpow_nonneg hY.le _)
          (mul_nonneg (by norm_num) (Real.log_pos hT).le)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hcoefficient
      exact integral_typeIITwistedNorm_restrict_le_localFourthMoment M rho hR

/-- Unconditional source-window local fourth-moment charge for every sufficiently large
source height. The corrected Gamma-tail producer has discharged the truncation premises. -/
theorem eventually_one_sixth_le_source_typeIILocalFourthMoment :
    ∀ᶠ T : ℝ in atTop,
      ∀ (sigma : ℝ) {rho : ℂ},
        1 / 2 + 1 / Real.log T ≤ sigma →
        IsNontrivialZero rho →
        T ≤ rho.im → rho.im ≤ 2 * T → sigma ≤ rho.re →
        ClassicalDetectorTypeII
          (classicalDetectorSourceM T) (classicalDetectorSourceY T) rho →
        (1 / 6 : ℝ) ≤
          ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
            (classicalDetectorSourceY T ^ (1 / 2 - rho.re) *
              (2 * Real.log T) *
              ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
                (maynardPrattTypeIILocalFourthMoment
                    (classicalDetectorSourceM T) rho
                    (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ))) := by
  filter_upwards
    [eventually_maynardPrattTypeIIContourNormTailMass_source_le_one,
      eventually_gt_atTop (1 : ℝ)] with T htailAll hT
  intro sigma rho hsigma hrho himLower himUpper hrhoSigma hII
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hbeta : 1 / 2 < rho.re := by
    have hinv : 0 < 1 / Real.log T := one_div_pos.mpr hlogT
    linarith
  have hY :
      0 < classicalDetectorSourceY T := by
    rw [classicalDetectorSourceY]
    exact Real.sqrt_pos.2 (zero_lt_one.trans hT)
  let delta : ℝ :=
    maynardPrattTypeIIContourNormTailMass
      (classicalDetectorSourceM T) rho
      (classicalDetectorSourceY T) (Real.log T ^ (2 : ℕ))
  have htailOne : delta ≤ 1 := by
    exact htailAll hrho hbeta himLower himUpper
  have htrunc :
      maynardPrattTypeIIContourNormMass
          (classicalDetectorSourceM T) rho
          (classicalDetectorSourceY T) ≤
        maynardPrattTypeIIContourNormMassOn
            (classicalDetectorSourceM T) rho
            (classicalDetectorSourceY T) (Real.log T ^ (2 : ℕ)) +
          delta := by
    exact (maynardPrattTypeIIContourNormMass_eq_on_add_tail
      (classicalDetectorSourceM T) hrho hbeta hY
      (Real.log T ^ (2 : ℕ))).le
  have hdelta :
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ * delta ≤ 1 / 6 := by
    calc
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ * delta ≤
          ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ * 1 :=
        mul_le_mul_of_nonneg_left htailOne (norm_nonneg _)
      _ = ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ := by ring
      _ ≤ 1 / 6 := norm_inv_two_pi_le_one_sixth
  exact
    one_sixth_le_normScale_mul_rpow_mul_log_mul_typeIILocalFourthMoment
      hT hY (sq_nonneg (Real.log T)) hsigma hrho hrhoSigma hII
      htrunc hdelta

end

end LeanLab.Riemann
