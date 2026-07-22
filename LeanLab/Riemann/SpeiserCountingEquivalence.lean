import LeanLab.Riemann.BurnolFiniteLowerBound
import LeanLab.Riemann.DeBruijnNewmanPolymathCriterion
import LeanLab.Riemann.WeilCompactPositivityCriterion
import Mathlib.Analysis.Meromorphic.Divisor

set_option linter.style.header false

/-!
# Speiser's criterion through multiplicity-bearing zero counts

This file builds the zero-counting interface used in the rigorous Levinson--Montgomery proof of
Speiser's criterion.  The analytic theorem producing an unbounded sequence of exact equal counts
is not assumed here: it is exposed as an explicit proposition consumed by a separate theorem.
-/

namespace LeanLab.Riemann

open Complex Function Set
open scoped BigOperators Topology

noncomputable section

/-- The open upper-left half of the critical strip used by Levinson--Montgomery. -/
def speiserUpperLeftStrip : Set ℂ :=
  {s : ℂ | 0 < s.im ∧ 0 < s.re ∧ s.re < 1 / 2}

/-- The portion of the upper-left strip below height `T`. -/
def speiserUpperLeftRectangle (T : ℝ) : Set ℂ :=
  {s : ℂ | s ∈ speiserUpperLeftStrip ∧ s.im < T}

/-- Speiser's derivative-zero-free condition in the source counting region. -/
def SpeiserDerivativeZeroFree : Prop :=
  ∀ s : ℂ, s ∈ speiserUpperLeftStrip → deriv riemannZeta s ≠ 0

/-- The corresponding zeta-zero-free condition in the source counting region. -/
def SpeiserZetaZeroFree : Prop :=
  ∀ s : ℂ, s ∈ speiserUpperLeftStrip → riemannZeta s ≠ 0

theorem analyticOnNhd_deriv_riemannZeta :
    AnalyticOnNhd ℂ (deriv riemannZeta) ({1} : Set ℂ)ᶜ :=
  analyticOn_riemannZeta.deriv

theorem deriv_riemannZeta_zero_ne_zero :
    deriv riemannZeta 0 ≠ 0 := by
  rw [deriv_riemannZeta_zero]
  apply div_ne_zero
  · apply neg_ne_zero.mpr
    intro hlog
    have hre := congrArg Complex.re hlog
    have hcast : (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hcast] at hre
    rw [Complex.log_ofReal_re] at hre
    norm_num only [Complex.zero_re] at hre
    exact (Real.log_pos (by nlinarith [Real.pi_gt_three])).ne' hre
  · norm_num

theorem analyticOrderAt_deriv_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt (deriv riemannZeta) s ≠ ⊤ := by
  have hconnected : IsPreconnected (({1} : Set ℂ)ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have horderZero : analyticOrderAt (deriv riemannZeta) (0 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr deriv_riemannZeta_zero_ne_zero)]
    exact ENat.zero_ne_top
  exact analyticOnNhd_deriv_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    hconnected (by simp) (by simpa using hs) horderZero

/-- The natural order of a zero of `zeta'`, finite away from the zeta pole. -/
def riemannZetaDerivZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt (deriv riemannZeta) s

theorem riemannZetaDerivZeroMultiplicity_pos_iff {s : ℂ} (hs : s ≠ 1) :
    0 < riemannZetaDerivZeroMultiplicity s ↔ deriv riemannZeta s = 0 := by
  constructor
  · intro hpos
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_of_gt hpos)
  · intro hzero
    apply Nat.pos_of_ne_zero
    intro horder
    have hfinite := analyticOrderAt_deriv_riemannZeta_ne_top hs
    have hne : analyticOrderAt (deriv riemannZeta) s ≠ 0 :=
      (analyticOnNhd_deriv_riemannZeta s (by simpa using hs)).analyticOrderAt_ne_zero.mpr hzero
    apply hne
    change analyticOrderNatAt (deriv riemannZeta) s = 0 at horder
    rw [← Nat.cast_analyticOrderNatAt hfinite, horder]
    simp

/-- The locally finite divisor of `zeta'` on the complement of the zeta pole. -/
def riemannZetaDerivDivisor : Function.locallyFinsuppWithin (({1} : Set ℂ)ᶜ) ℤ :=
  MeromorphicOn.divisor (deriv riemannZeta) (({1} : Set ℂ)ᶜ)

theorem riemannZetaDerivDivisor_apply {s : ℂ} (hs : s ≠ 1) :
    riemannZetaDerivDivisor s = (riemannZetaDerivZeroMultiplicity s : ℤ) := by
  rw [riemannZetaDerivDivisor,
    MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_deriv_riemannZeta
      (by simpa using hs),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_deriv_riemannZeta_ne_top hs)]
  simp [riemannZetaDerivZeroMultiplicity]

theorem mem_support_riemannZetaDerivDivisor_iff {s : ℂ} (hs : s ≠ 1) :
    s ∈ Function.support riemannZetaDerivDivisor ↔ deriv riemannZeta s = 0 := by
  rw [Function.mem_support, riemannZetaDerivDivisor_apply hs]
  constructor
  · intro hne
    exact (riemannZetaDerivZeroMultiplicity_pos_iff hs).mp
      (Nat.pos_of_ne_zero (by exact_mod_cast hne))
  · intro hzero
    have hpos := (riemannZetaDerivZeroMultiplicity_pos_iff hs).mpr hzero
    exact_mod_cast Nat.ne_of_gt hpos

private theorem speiserUpperLeftRectangle_subset_compactRectangle (T : ℝ) :
    speiserUpperLeftRectangle T ⊆
      Set.Icc (0 : ℝ) (1 / 2) ×ℂ Set.Icc (0 : ℝ) (max T 0) := by
  intro s hs
  change s.re ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ s.im ∈ Set.Icc (0 : ℝ) (max T 0)
  exact ⟨⟨hs.1.2.1.le, hs.1.2.2.le⟩,
    ⟨hs.1.1.le, hs.2.le.trans (le_max_left T 0)⟩⟩

/-- Zeta zeros in a bounded upper-left rectangle form a finite set. -/
theorem finite_speiserUpperLeftZetaZeroSet (T : ℝ) :
    ({s : ℂ | s ∈ speiserUpperLeftRectangle T ∧ IsNontrivialZero s} : Set ℂ).Finite := by
  let K : Set ℂ := Set.Icc (0 : ℝ) (1 / 2) ×ℂ Set.Icc (0 : ℝ) (max T 0)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply (compact_inter_nontrivialZeros_finite hK).subset
  intro s hs
  exact ⟨speiserUpperLeftRectangle_subset_compactRectangle T hs.1, hs.2⟩

/-- Zeros of `zeta'` in a bounded upper-left rectangle form a finite set. -/
theorem finite_speiserUpperLeftDerivZeroSet (T : ℝ) :
    ({s : ℂ | s ∈ speiserUpperLeftRectangle T ∧ deriv riemannZeta s = 0} : Set ℂ).Finite := by
  let K : Set ℂ := Set.Icc (0 : ℝ) (1 / 2) ×ℂ Set.Icc (0 : ℝ) (max T 0)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKDomain : K ⊆ (({1} : Set ℂ)ᶜ) := by
    intro s hs hsOne
    subst s
    change (1 : ℂ).re ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      (1 : ℂ).im ∈ Set.Icc (0 : ℝ) (max T 0) at hs
    norm_num at hs
  have hAnalyticK : AnalyticOnNhd ℂ (deriv riemannZeta) K :=
    analyticOnNhd_deriv_riemannZeta.mono hKDomain
  apply ((MeromorphicOn.divisor (deriv riemannZeta) K).finiteSupport hK).subset
  intro s hs
  have hsK := speiserUpperLeftRectangle_subset_compactRectangle T hs.1
  rw [Function.mem_support]
  have hsOne : s ≠ 1 := hKDomain hsK
  have hdivisor :
      MeromorphicOn.divisor (deriv riemannZeta) K s =
        (riemannZetaDerivZeroMultiplicity s : ℤ) := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnalyticK hsK,
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_deriv_riemannZeta_ne_top hsOne)]
    simp [riemannZetaDerivZeroMultiplicity]
  rw [hdivisor]
  exact_mod_cast Nat.ne_of_gt
    ((riemannZetaDerivZeroMultiplicity_pos_iff hsOne).mpr hs.2)

/-- The finite zeta-zero set in the source rectangle. -/
def speiserUpperLeftZetaZeroFinset (T : ℝ) : Finset ℂ :=
  (finite_speiserUpperLeftZetaZeroSet T).toFinset

/-- The finite derivative-zero set in the source rectangle. -/
def speiserUpperLeftDerivZeroFinset (T : ℝ) : Finset ℂ :=
  (finite_speiserUpperLeftDerivZeroSet T).toFinset

@[simp] theorem mem_speiserUpperLeftZetaZeroFinset {T : ℝ} {s : ℂ} :
    s ∈ speiserUpperLeftZetaZeroFinset T ↔
      s ∈ speiserUpperLeftRectangle T ∧ IsNontrivialZero s := by
  classical
  simp [speiserUpperLeftZetaZeroFinset]

@[simp] theorem mem_speiserUpperLeftDerivZeroFinset {T : ℝ} {s : ℂ} :
    s ∈ speiserUpperLeftDerivZeroFinset T ↔
      s ∈ speiserUpperLeftRectangle T ∧ deriv riemannZeta s = 0 := by
  classical
  simp [speiserUpperLeftDerivZeroFinset]

/-- Levinson--Montgomery's multiplicity-bearing left zeta-zero count. -/
def speiserUpperLeftZetaZeroCount (T : ℝ) : ℕ :=
  ∑ s ∈ speiserUpperLeftZetaZeroFinset T, burnolZetaZeroMultiplicity s

/-- Levinson--Montgomery's multiplicity-bearing left derivative-zero count. -/
def speiserUpperLeftDerivZeroCount (T : ℝ) : ℕ :=
  ∑ s ∈ speiserUpperLeftDerivZeroFinset T, riemannZetaDerivZeroMultiplicity s

theorem speiserUpperLeftZetaZeroCount_pos_of_zero {T : ℝ} {s : ℂ}
    (hs : s ∈ speiserUpperLeftRectangle T) (hzero : IsNontrivialZero s) :
    0 < speiserUpperLeftZetaZeroCount T := by
  classical
  unfold speiserUpperLeftZetaZeroCount
  refine Finset.sum_pos' (fun z _ ↦ Nat.zero_le _) ⟨s, ?_, ?_⟩
  · exact mem_speiserUpperLeftZetaZeroFinset.mpr ⟨hs, hzero⟩
  · exact burnolZetaZeroMultiplicity_pos hzero

theorem speiserUpperLeftDerivZeroCount_pos_of_zero {T : ℝ} {s : ℂ}
    (hs : s ∈ speiserUpperLeftRectangle T) (hzero : deriv riemannZeta s = 0) :
    0 < speiserUpperLeftDerivZeroCount T := by
  classical
  unfold speiserUpperLeftDerivZeroCount
  have hsOne : s ≠ 1 := by
    intro hsEq
    subst s
    norm_num [speiserUpperLeftRectangle, speiserUpperLeftStrip] at hs
  refine Finset.sum_pos' (fun z _ ↦ Nat.zero_le _) ⟨s, ?_, ?_⟩
  · exact mem_speiserUpperLeftDerivZeroFinset.mpr ⟨hs, hzero⟩
  · exact (riemannZetaDerivZeroMultiplicity_pos_iff hsOne).mpr hzero

theorem speiserUpperLeftDerivZeroCount_eq_zero
    (hfree : SpeiserDerivativeZeroFree) (T : ℝ) :
    speiserUpperLeftDerivZeroCount T = 0 := by
  classical
  unfold speiserUpperLeftDerivZeroCount
  apply Finset.sum_eq_zero
  intro s hs
  have hsData := mem_speiserUpperLeftDerivZeroFinset.mp hs
  exact (hfree s hsData.1.1 hsData.2).elim

theorem speiserUpperLeftZetaZeroCount_eq_zero
    (hfree : SpeiserZetaZeroFree) (T : ℝ) :
    speiserUpperLeftZetaZeroCount T = 0 := by
  classical
  unfold speiserUpperLeftZetaZeroCount
  apply Finset.sum_eq_zero
  intro s hs
  have hsData := mem_speiserUpperLeftZetaZeroFinset.mp hs
  exact (hfree s hsData.1.1 hsData.2.1).elim

/-- The elementary real-axis input needed because the source counts only positive heights. -/
def CriticalStripRealAxisZeroFree : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → s.im ≠ 0

/-- The real-axis base fact follows from positivity of the source-normalized de Bruijn--Newman
transform on the imaginary axis. -/
theorem criticalStripRealAxisZeroFree :
    CriticalStripRealAxisZeroFree := by
  intro s hs hsIm
  let y : ℝ := 1 - 2 * s.re
  have harg : (1 + I * ((y : ℂ) * I)) / 2 = s := by
    apply Complex.ext
    · simp [y]
    · simp [hsIm]
  have hH := deBruijnNewmanH_zero_eq_riemannXi ((y : ℂ) * I)
  rw [harg, (isNontrivialZero_iff_riemannXi_eq_zero s).mp hs] at hH
  have hHzero : deBruijnNewmanH 0 ((y : ℂ) * I) = 0 := by
    simpa using hH
  have hpos := deBruijnNewmanH_mul_I_re_pos 0 y
  rw [hHzero, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

theorem isNontrivialZero_of_mem_speiserUpperLeftStrip {s : ℂ}
    (hs : s ∈ speiserUpperLeftStrip) (hzero : riemannZeta s = 0) :
    IsNontrivialZero s := by
  refine ⟨hzero, ?_, ?_⟩
  · intro htrivial
    rcases htrivial with ⟨n, rfl⟩
    norm_num [speiserUpperLeftStrip] at hs
  · intro hsOne
    subst s
    norm_num [speiserUpperLeftStrip] at hs

theorem RiemannHypothesis.speiserZetaZeroFree
    (hRH : RiemannHypothesis) :
    SpeiserZetaZeroFree := by
  intro s hs hzero
  have hsNontrivial := isNontrivialZero_of_mem_speiserUpperLeftStrip hs hzero
  have hline : s.re = 1 / 2 := hRH s hzero hsNontrivial.2.1 hsNontrivial.2.2
  exact (ne_of_lt hs.2.2) hline

theorem speiser_isNontrivialZero_one_sub {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (1 - s) := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero]
  rw [riemannXi_one_sub]
  exact (isNontrivialZero_iff_riemannXi_eq_zero s).mp hs

theorem speiser_nontrivial_zero_re_pos {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re := by
  have hreflect := nontrivial_zero_re_lt_one (speiser_isNontrivialZero_one_sub hs)
  simp only [sub_re, one_re] at hreflect
  linarith

theorem exists_speiserUpperLeftZero_of_nontrivialZero_re_lt_half
    {s : ℂ} (hs : IsNontrivialZero s) (hsIm : s.im ≠ 0) (hsRe : s.re < 1 / 2) :
    ∃ rho : ℂ, rho ∈ speiserUpperLeftStrip ∧ IsNontrivialZero rho := by
  have hsRePos := speiser_nontrivial_zero_re_pos hs
  by_cases hsImPos : 0 < s.im
  · exact ⟨s, ⟨hsImPos, hsRePos, hsRe⟩, hs⟩
  · have hsImNeg : s.im < 0 :=
      lt_of_le_of_ne (le_of_not_gt hsImPos) hsIm
    refine ⟨(starRingEnd ℂ) s, ?_, isNontrivialZero_conj hs⟩
    simp only [starRingEnd_apply]
    exact ⟨neg_pos.mpr hsImNeg, hsRePos, hsRe⟩

theorem riemannHypothesis_of_speiserZetaZeroFree
    (hfree : SpeiserZetaZeroFree) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro s hs
  rw [OnCriticalLine]
  by_contra hsLine
  rcases lt_or_gt_of_ne hsLine with hsLeft | hsRight
  · obtain ⟨rho, hrhoStrip, hrhoZero⟩ :=
      exists_speiserUpperLeftZero_of_nontrivialZero_re_lt_half
        hs (criticalStripRealAxisZeroFree s hs) hsLeft
    exact hfree rho hrhoStrip hrhoZero.1
  · have hreflect : IsNontrivialZero (1 - s) := speiser_isNontrivialZero_one_sub hs
    have hreflectRe : (1 - s).re < 1 / 2 := by
      simp only [sub_re, one_re]
      linarith
    obtain ⟨rho, hrhoStrip, hrhoZero⟩ :=
      exists_speiserUpperLeftZero_of_nontrivialZero_re_lt_half
        hreflect (criticalStripRealAxisZeroFree (1 - s) hreflect) hreflectRe
    exact hfree rho hrhoStrip hrhoZero.1

theorem riemannHypothesis_iff_speiserZetaZeroFree :
    RiemannHypothesis ↔ SpeiserZetaZeroFree :=
  ⟨RiemannHypothesis.speiserZetaZeroFree,
    riemannHypothesis_of_speiserZetaZeroFree⟩

/-- The exact-count subsequence statement isolated from Levinson--Montgomery's analytic proof. -/
def LevinsonMontgomeryExactCountSequence : Prop :=
  ∀ B : ℝ, ∃ T : ℝ, B < T ∧
    speiserUpperLeftDerivZeroCount T = speiserUpperLeftZetaZeroCount T

/-- The source `O(log T)` estimate, weakened to exactly the sublinear consequence used below. -/
def LevinsonMontgomeryCountDifferenceSublinear : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
    |(speiserUpperLeftDerivZeroCount T : ℝ) -
        (speiserUpperLeftZetaZeroCount T : ℝ)| ≤ epsilon * T

/-- The literal `O(log T)`-shaped count estimate appearing in Levinson--Montgomery Theorem 1. -/
def LevinsonMontgomeryLogCountBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
    |(speiserUpperLeftDerivZeroCount T : ℝ) -
        (speiserUpperLeftZetaZeroCount T : ℝ)| ≤ C * Real.log T

theorem levinsonMontgomeryCountDifferenceSublinear_of_logCountBound
    (hlogBound : LevinsonMontgomeryLogCountBound) :
    LevinsonMontgomeryCountDifferenceSublinear := by
  rcases hlogBound with ⟨C, hC, Tsource, hsource⟩
  intro epsilon hepsilon
  have hClog : (fun T : ℝ ↦ C * Real.log T) =o[Filter.atTop] (fun T : ℝ ↦ T) := by
    simpa only [Function.id_def] using Real.isLittleO_log_id_atTop.const_mul_left C
  have heventual := Asymptotics.isLittleO_iff.mp hClog hepsilon
  rw [Filter.eventually_atTop] at heventual
  obtain ⟨Tlog, hlogEventually⟩ := heventual
  refine ⟨max Tsource (max Tlog 1), fun T hT ↦ ?_⟩
  have hTsource : Tsource ≤ T := (le_max_left _ _).trans hT
  have hTlog : Tlog ≤ T :=
    (le_max_left Tlog 1).trans ((le_max_right Tsource (max Tlog 1)).trans hT)
  have hTone : 1 ≤ T :=
    (le_max_right Tlog 1).trans ((le_max_right Tsource (max Tlog 1)).trans hT)
  have hsourceT := hsource T hTsource
  have hlittle := hlogEventually T hTlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hTone),
    abs_of_nonneg (mul_nonneg hC (Real.log_nonneg hTone))] at hlittle
  exact hsourceT.trans hlittle

/-- The exact alternative in the Levinson--Montgomery proof: either exact equality recurs at
unbounded heights, or left zeta zeros are eventually more numerous than `T / 2`. -/
def LevinsonMontgomeryCountDichotomy : Prop :=
  LevinsonMontgomeryExactCountSequence ∨
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
      T / 2 < (speiserUpperLeftZetaZeroCount T : ℝ)

theorem levinsonMontgomeryExactCountSequence_of_zetaCount_eq_zero
    (hdichotomy : LevinsonMontgomeryCountDichotomy)
    (hzeta : ∀ T : ℝ, speiserUpperLeftZetaZeroCount T = 0) :
    LevinsonMontgomeryExactCountSequence := by
  rcases hdichotomy with hexact | ⟨T0, hdense⟩
  · exact hexact
  · let T : ℝ := max 0 T0 + 1
    have hT0 : T0 ≤ T := by
      dsimp only [T]
      linarith [le_max_right 0 T0]
    have hTpos : 0 < T := by
      dsimp only [T]
      linarith [le_max_left 0 T0]
    have h := hdense T hT0
    rw [hzeta T] at h
    norm_num at h
    linarith

theorem levinsonMontgomeryExactCountSequence_of_derivCount_eq_zero
    (hsublinear : LevinsonMontgomeryCountDifferenceSublinear)
    (hdichotomy : LevinsonMontgomeryCountDichotomy)
    (hderiv : ∀ T : ℝ, speiserUpperLeftDerivZeroCount T = 0) :
    LevinsonMontgomeryExactCountSequence := by
  rcases hdichotomy with hexact | ⟨Tdense, hdense⟩
  · exact hexact
  · obtain ⟨Tsub, hsub⟩ := hsublinear (1 / 4) (by norm_num)
    let T : ℝ := max 0 (max Tdense Tsub) + 1
    have hTdense : Tdense ≤ T := by
      dsimp only [T]
      linarith [le_max_right 0 (max Tdense Tsub), le_max_left Tdense Tsub]
    have hTsub : Tsub ≤ T := by
      dsimp only [T]
      linarith [le_max_right 0 (max Tdense Tsub), le_max_right Tdense Tsub]
    have hTpos : 0 < T := by
      dsimp only [T]
      linarith [le_max_left 0 (max Tdense Tsub)]
    have hlarge := hdense T hTdense
    have hsmall := hsub T hTsub
    rw [hderiv T] at hsmall
    norm_num only [Nat.cast_zero, zero_sub, abs_neg, Nat.cast_nonneg, abs_of_nonneg,
      one_div] at hsmall
    linarith

/-- Exact equal counts on unbounded heights eliminate the last upper-left zeta zero. -/
theorem speiserZetaZeroFree_of_derivZeroFree_of_exactCountSequence
    (hfree : SpeiserDerivativeZeroFree)
    (hexact : LevinsonMontgomeryExactCountSequence) :
    SpeiserZetaZeroFree := by
  intro s hsStrip hsZero
  have hsNontrivial := isNontrivialZero_of_mem_speiserUpperLeftStrip hsStrip hsZero
  obtain ⟨T, hsT, hcounts⟩ := hexact s.im
  have hpositive := speiserUpperLeftZetaZeroCount_pos_of_zero
    (T := T) (s := s) ⟨hsStrip, hsT⟩ hsNontrivial
  have hderivZero := speiserUpperLeftDerivZeroCount_eq_zero hfree T
  omega

theorem speiserDerivativeZeroFree_of_riemannHypothesis_of_exactCountSequence
    (hRH : RiemannHypothesis)
    (hexact : LevinsonMontgomeryExactCountSequence) :
    SpeiserDerivativeZeroFree := by
  intro s hsStrip hsZero
  obtain ⟨T, hsT, hcounts⟩ := hexact s.im
  have hpositive := speiserUpperLeftDerivZeroCount_pos_of_zero
    (T := T) (s := s) ⟨hsStrip, hsT⟩ hsZero
  have hzetaZero := speiserUpperLeftZetaZeroCount_eq_zero
    (RiemannHypothesis.speiserZetaZeroFree hRH) T
  omega

/-- The exact-count sequence closes the reverse Speiser implication. -/
theorem riemannHypothesis_of_speiserDerivativeZeroFree_of_exactCountSequence
    (hexact : LevinsonMontgomeryExactCountSequence)
    (hfree : SpeiserDerivativeZeroFree) :
    RiemannHypothesis :=
  riemannHypothesis_of_speiserZetaZeroFree
    (speiserZetaZeroFree_of_derivZeroFree_of_exactCountSequence hfree hexact)

/-- The full logical consumer of the two source-faithful Levinson--Montgomery counting steps. -/
theorem riemannHypothesis_iff_speiserDerivativeZeroFree_of_levinsonMontgomeryCounts
    (hsublinear : LevinsonMontgomeryCountDifferenceSublinear)
    (hdichotomy : LevinsonMontgomeryCountDichotomy) :
    RiemannHypothesis ↔ SpeiserDerivativeZeroFree := by
  constructor
  · intro hRH
    apply speiserDerivativeZeroFree_of_riemannHypothesis_of_exactCountSequence hRH
    exact levinsonMontgomeryExactCountSequence_of_zetaCount_eq_zero hdichotomy
      (speiserUpperLeftZetaZeroCount_eq_zero
        (RiemannHypothesis.speiserZetaZeroFree hRH))
  · intro hfree
    exact riemannHypothesis_of_speiserDerivativeZeroFree_of_exactCountSequence
      (levinsonMontgomeryExactCountSequence_of_derivCount_eq_zero
        hsublinear hdichotomy (speiserUpperLeftDerivZeroCount_eq_zero hfree)) hfree

/-- Speiser's equivalence follows from the two exact analytic outputs of Levinson--Montgomery
Theorem 1. -/
theorem riemannHypothesis_iff_speiserDerivativeZeroFree_of_levinsonMontgomeryTheoremOne
    (hlogBound : LevinsonMontgomeryLogCountBound)
    (hdichotomy : LevinsonMontgomeryCountDichotomy) :
    RiemannHypothesis ↔ SpeiserDerivativeZeroFree :=
  riemannHypothesis_iff_speiserDerivativeZeroFree_of_levinsonMontgomeryCounts
    (levinsonMontgomeryCountDifferenceSublinear_of_logCountBound hlogBound) hdichotomy

end

end LeanLab.Riemann
