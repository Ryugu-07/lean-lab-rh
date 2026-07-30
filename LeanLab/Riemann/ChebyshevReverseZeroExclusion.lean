import LeanLab.Riemann.ChebyshevMellin
import LeanLab.Riemann.LiReverseCriterion
import LeanLab.Riemann.ZetaConvexity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.MellinTransform

set_option linter.style.header false

/-!
# The reverse Chebyshev--von Koch zero-exclusion argument

An `O(N^r)` bound for `Chebyshev.psi N - N` makes the naturally ordered error Mellin
value holomorphic on `Re(s) > r`.  After removing the zeta pole, analytic continuation and
zero-order comparison exclude zeta zeros in that half-plane.
-/

namespace LeanLab.Riemann

open Asymptotics Complex Filter MeasureTheory Set
open scoped LSeries.notation Topology

noncomputable section

/-- The real-axis floor error used by the Abel--Mellin representation. -/
def chebyshevPsiFloorError (t : ℝ) : ℂ :=
  ((Chebyshev.psi t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)

/-- A positive-axis extension supported exactly on the source integration range `t > 1`. -/
def chebyshevPsiFloorErrorExtension (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator chebyshevPsiFloorError t

/-- The candidate holomorphic continuation of the Chebyshev error Dirichlet series. -/
def chebyshevPsiErrorContinuation (s : ℂ) : ℂ :=
  s * mellin chebyshevPsiFloorErrorExtension (-s)

theorem locallyIntegrable_chebyshevPsiFloorError :
    LocallyIntegrable chebyshevPsiFloorError := by
  have hpsi : LocallyIntegrable (fun t : ℝ => Chebyshev.psi t) :=
    Chebyshev.psi_mono.locallyIntegrable
  have hfloor : LocallyIntegrable (fun t : ℝ => (⌊t⌋₊ : ℝ)) := by
    have hmono : Monotone (fun t : ℝ => (⌊t⌋₊ : ℝ)) := by
      intro a b hab
      change (⌊a⌋₊ : ℝ) ≤ (⌊b⌋₊ : ℝ)
      exact_mod_cast Nat.floor_mono hab
    exact hmono.locallyIntegrable
  have hreal :
      LocallyIntegrable
        (fun t : ℝ => Chebyshev.psi t - (⌊t⌋₊ : ℝ)) :=
    hpsi.sub hfloor
  intro x
  obtain ⟨u, hu, hint⟩ := hreal x
  refine ⟨u, hu, ?_⟩
  change IntegrableOn
    (fun t : ℝ => ((Chebyshev.psi t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)) u volume
  exact hint.ofReal

theorem locallyIntegrable_chebyshevPsiFloorErrorExtension :
    LocallyIntegrable chebyshevPsiFloorErrorExtension := by
  exact locallyIntegrable_chebyshevPsiFloorError.indicator measurableSet_Ioi

theorem chebyshevPsiFloorError_isBigO_of_nat_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr : 0 ≤ r) :
    chebyshevPsiFloorError =O[atTop] fun t : ℝ => t ^ r := by
  have hfloor :
      (fun t : ℝ =>
        (Chebyshev.psi ⌊t⌋₊ : ℂ) - (⌊t⌋₊ : ℂ)) =O[atTop]
          fun t : ℝ => (⌊t⌋₊ : ℝ) ^ r :=
    hO.comp_tendsto tendsto_nat_floor_atTop
  have hsource :
      chebyshevPsiFloorError =O[atTop]
        fun t : ℝ => (⌊t⌋₊ : ℝ) ^ r := by
    refine hfloor.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    rw [chebyshevPsiFloorError, Chebyshev.psi_eq_psi_coe_floor]
    push_cast
    rfl
  exact hsource.trans
    (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))

theorem chebyshevPsiFloorErrorExtension_isBigO_of_nat_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr : 0 ≤ r) :
    chebyshevPsiFloorErrorExtension =O[atTop]
      fun t : ℝ => t ^ r := by
  refine (chebyshevPsiFloorError_isBigO_of_nat_isBigO hO hr).congr'
    ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  simp [chebyshevPsiFloorErrorExtension, show (1 : ℝ) < t by linarith]

theorem chebyshevPsiFloorErrorExtension_isBigO_nhdsGT_zero
    (b : ℝ) :
    chebyshevPsiFloorErrorExtension =O[𝓝[>] (0 : ℝ)]
      fun t : ℝ => t ^ b := by
  refine (isBigO_zero (fun t : ℝ => t ^ b) (𝓝[>] (0 : ℝ))).congr'
    ?_ EventuallyEq.rfl
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left
  filter_upwards [hlt] with t ht
  simp [chebyshevPsiFloorErrorExtension, not_lt_of_ge ht.le]

/-- The Chebyshev error continuation is holomorphic at every point strictly to the right of
the exponent supplied by the partial-sum estimate. -/
theorem differentiableAt_chebyshevPsiErrorContinuation_of_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re) :
    DifferentiableAt ℂ chebyshevPsiErrorContinuation s := by
  let b : ℝ := -s.re - 1
  have hmellin :
      DifferentiableAt ℂ
        (mellin chebyshevPsiFloorErrorExtension) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (a := -r) (b := b)
    · exact
        locallyIntegrable_chebyshevPsiFloorErrorExtension.locallyIntegrableOn
          (Ioi 0)
    · simpa only [neg_neg] using
        chebyshevPsiFloorErrorExtension_isBigO_of_nat_isBigO hO hr
    · simp only [neg_re]
      linarith
    · simpa only [neg_neg] using
        chebyshevPsiFloorErrorExtension_isBigO_nhdsGT_zero (-b)
    · simp only [neg_re, b]
      linarith
  have hcomp :
      DifferentiableAt ℂ
        (fun z : ℂ => mellin chebyshevPsiFloorErrorExtension (-z)) s := by
    change DifferentiableAt ℂ
      (mellin chebyshevPsiFloorErrorExtension ∘ fun z : ℂ => -z) s
    exact hmellin.comp s differentiableAt_id.neg
  exact differentiableAt_id.mul hcomp

theorem mellin_chebyshevPsiFloorErrorExtension_neg
    (s : ℂ) :
    mellin chebyshevPsiFloorErrorExtension (-s) =
      ∫ t in Ioi (1 : ℝ),
        chebyshevPsiFloorError t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases ht : 1 < t
    · have ht0 : 0 < t := zero_lt_one.trans ht
      have htmem : t ∈ Ioi (1 : ℝ) := ht
      have ht0mem : t ∈ Ioi (0 : ℝ) := ht0
      rw [indicator_of_mem ht0mem, indicator_of_mem htmem]
      simp only [chebyshevPsiFloorErrorExtension]
      rw [indicator_of_mem htmem]
      simp only [smul_eq_mul]
      rw [show -s - 1 = -(s + 1) by ring]
      ring
    · by_cases ht0 : 0 < t
      · simp [chebyshevPsiFloorErrorExtension, ht, ht0]
      · simp [chebyshevPsiFloorErrorExtension, ht, ht0]

/-- On the common absolute-convergence half-plane, the continuation is the actual error
L-series. -/
theorem chebyshevPsiErrorContinuation_eq_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    chebyshevPsiErrorContinuation s =
      LSeries chebyshevPsiErrorCoeff s := by
  rw [chebyshevPsiErrorContinuation,
    mellin_chebyshevPsiFloorErrorExtension_neg]
  rw [LSeries_chebyshevPsiErrorCoeff_eq_mellin hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change
    ((Chebyshev.psi t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) *
        (t : ℂ) ^ (-(s + 1)) =
      ((Chebyshev.psi t : ℂ) - (⌊t⌋₊ : ℂ)) *
        (t : ℂ) ^ (-(s + 1))
  push_cast
  ring

/-- The half-plane on which an exponent-`r` Chebyshev estimate continues the error series. -/
def chebyshevErrorHalfPlane (r : ℝ) : Set ℂ :=
  {s : ℂ | r < s.re}

theorem isOpen_chebyshevErrorHalfPlane (r : ℝ) :
    IsOpen (chebyshevErrorHalfPlane r) := by
  exact isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_chebyshevErrorHalfPlane (r : ℝ) :
    IsPreconnected (chebyshevErrorHalfPlane r) := by
  simpa only [chebyshevErrorHalfPlane] using
    (convex_halfSpace_re_gt r).isPreconnected

theorem analyticOnNhd_chebyshevPsiErrorContinuation_of_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr : 0 ≤ r) :
    AnalyticOnNhd ℂ chebyshevPsiErrorContinuation
      (chebyshevErrorHalfPlane r) := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact
      (differentiableAt_chebyshevPsiErrorContinuation_of_isBigO
        hO hr hs).differentiableWithinAt
  · exact isOpen_chebyshevErrorHalfPlane r

/-- Away from the original zeta pole, differentiate the entire pole-removed extension by its
literal product formula. -/
theorem deriv_zetaPoleRemoved_eq
    {s : ℂ} (hs : s ≠ 1) :
    deriv zetaPoleRemoved s =
      riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev :
      zetaPoleRemoved =ᶠ[𝓝 s]
        fun w : ℂ => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact zetaPoleRemoved_eq (by simpa using hw)
  rw [hev.deriv_eq]
  have hlinear :
      HasDerivAt (fun w : ℂ => w - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have hzeta :
      HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  change deriv ((fun w : ℂ => w - 1) * riemannZeta) s =
    riemannZeta s + (s - 1) * deriv riemannZeta s
  simpa only [Pi.mul_apply, one_mul] using (hlinear.mul hzeta).deriv

/-- The pole-removed differential equation on the initial absolute-convergence half-plane. -/
theorem chebyshevPoleRemovedODE_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * deriv zetaPoleRemoved s =
      zetaPoleRemoved s *
        (1 - (s - 1) * chebyshevPsiErrorContinuation s -
          zetaPoleRemoved s) := by
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have herror :
      chebyshevPsiErrorContinuation s =
        -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
    rw [chebyshevPsiErrorContinuation_eq_LSeries hs,
      LSeries_chebyshevPsiErrorCoeff_eq hs]
  rw [deriv_zetaPoleRemoved_eq hs1, zetaPoleRemoved_eq hs1, herror]
  field_simp [hzeta]
  ring

/-- Analytic continuation of the pole-removed differential equation to the whole
Chebyshev-controlled half-plane. -/
theorem chebyshevPoleRemovedODE_of_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    {s : ℂ} (hs : r < s.re) :
    (s - 1) * deriv zetaPoleRemoved s =
      zetaPoleRemoved s *
        (1 - (s - 1) * chebyshevPsiErrorContinuation s -
          zetaPoleRemoved s) := by
  let U : Set ℂ := chebyshevErrorHalfPlane r
  let lhs : ℂ → ℂ := fun z => (z - 1) * deriv zetaPoleRemoved z
  let rhs : ℂ → ℂ := fun z =>
    zetaPoleRemoved z *
      (1 - (z - 1) * chebyshevPsiErrorContinuation z -
        zetaPoleRemoved z)
  have herror :
      AnalyticOnNhd ℂ chebyshevPsiErrorContinuation U :=
    analyticOnNhd_chebyshevPsiErrorContinuation_of_isBigO hO hr0
  have hlhs : AnalyticOnNhd ℂ lhs U := by
    intro z hz
    exact
      (analyticAt_id.sub analyticAt_const).mul
        (differentiable_zetaPoleRemoved.analyticAt z).deriv
  have hrhs : AnalyticOnNhd ℂ rhs U := by
    intro z hz
    have hZ : AnalyticAt ℂ zetaPoleRemoved z :=
      differentiable_zetaPoleRemoved.analyticAt z
    have hE : AnalyticAt ℂ chebyshevPsiErrorContinuation z :=
      herror z hz
    exact hZ.mul
      ((analyticAt_const.sub
        ((analyticAt_id.sub analyticAt_const).mul hE)).sub hZ)
  have htwo : (2 : ℂ) ∈ U := by
    change r < (2 : ℂ).re
    norm_num
    linarith
  have heq : lhs =ᶠ[𝓝 (2 : ℂ)] rhs := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact chebyshevPoleRemovedODE_of_one_lt_re hz
  exact
    (hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs
      (isPreconnected_chebyshevErrorHalfPlane r) htwo heq) hs

theorem analyticOrderAt_zetaPoleRemoved_ne_top (s : ℂ) :
    analyticOrderAt zetaPoleRemoved s ≠ ⊤ := by
  have hZ :
      AnalyticOnNhd ℂ zetaPoleRemoved (Set.univ : Set ℂ) := by
    intro z _
    exact differentiable_zetaPoleRemoved.analyticAt z
  have hone :
      analyticOrderAt zetaPoleRemoved (1 : ℂ) ≠ ⊤ := by
    have hne : zetaPoleRemoved (1 : ℂ) ≠ 0 := by
      rw [zetaPoleRemoved_one]
      norm_num
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    exact ENat.zero_ne_top
  exact hZ.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s) hone

/-- The pole-removed ODE forbids a zero anywhere in the half-plane supplied by the Chebyshev
error exponent. -/
theorem zetaPoleRemoved_ne_zero_of_chebyshevPsiError_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    {s : ℂ} (hs : r < s.re) :
    zetaPoleRemoved s ≠ 0 := by
  intro hzero
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    simp at hzero
  have hZ : AnalyticAt ℂ zetaPoleRemoved s :=
    differentiable_zetaPoleRemoved.analyticAt s
  have hZderiv : AnalyticAt ℂ (deriv zetaPoleRemoved) s :=
    hZ.deriv
  have hfinite : analyticOrderAt zetaPoleRemoved s ≠ ⊤ :=
    analyticOrderAt_zetaPoleRemoved_ne_top s
  have horderNeZero : analyticOrderAt zetaPoleRemoved s ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hZ, hzero⟩
  let m : ℕ := analyticOrderNatAt zetaPoleRemoved s
  have hmcast :
      (m : ℕ∞) = analyticOrderAt zetaPoleRemoved s :=
    Nat.cast_analyticOrderNatAt hfinite
  have hmne : m ≠ 0 := by
    intro hm
    apply horderNeZero
    rw [← hmcast, hm]
    rfl
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have hZorder :
      analyticOrderAt zetaPoleRemoved s = (n + 1 : ℕ) := by
    rw [← hmcast, hn]
  have hderivOrder :
      analyticOrderAt (deriv zetaPoleRemoved) s = n :=
    analyticOrderAt_deriv_of_pos hZ hZorder
  let q : ℂ → ℂ := fun z =>
    1 - (z - 1) * chebyshevPsiErrorContinuation z -
      zetaPoleRemoved z
  have herror : AnalyticAt ℂ chebyshevPsiErrorContinuation s :=
    analyticOnNhd_chebyshevPsiErrorContinuation_of_isBigO
      hO hr0 s hs
  have hq : AnalyticAt ℂ q s := by
    exact
      (analyticAt_const.sub
        ((analyticAt_id.sub analyticAt_const).mul herror)).sub hZ
  have hlinear : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    analyticAt_id.sub analyticAt_const
  have hlinearOrder :
      analyticOrderAt (fun z : ℂ => z - 1) s = 0 := by
    exact hlinear.analyticOrderAt_eq_zero.mpr
      (sub_ne_zero.mpr hs1)
  have hleftOrder :
      analyticOrderAt
          (fun z : ℂ => (z - 1) * deriv zetaPoleRemoved z) s =
        n := by
    change analyticOrderAt
      ((fun z : ℂ => z - 1) * deriv zetaPoleRemoved) s = n
    rw [analyticOrderAt_mul hlinear hZderiv,
      hlinearOrder, zero_add, hderivOrder]
  have hrightOrder :
      analyticOrderAt (fun z : ℂ => zetaPoleRemoved z * q z) s =
        (n + 1 : ℕ∞) + analyticOrderAt q s := by
    change analyticOrderAt (zetaPoleRemoved * q) s =
      (n + 1 : ℕ∞) + analyticOrderAt q s
    rw [analyticOrderAt_mul hZ hq, hZorder]
    rfl
  have hODE :
      (fun z : ℂ => (z - 1) * deriv zetaPoleRemoved z) =ᶠ[𝓝 s]
        fun z : ℂ => zetaPoleRemoved z * q z := by
    have hopen : IsOpen (chebyshevErrorHalfPlane r) :=
      isOpen_chebyshevErrorHalfPlane r
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact chebyshevPoleRemovedODE_of_isBigO hO hr0 hr1 hz
  have horders :
      analyticOrderAt
          (fun z : ℂ => (z - 1) * deriv zetaPoleRemoved z) s =
        analyticOrderAt (fun z : ℂ => zetaPoleRemoved z * q z) s :=
    analyticOrderAt_congr hODE
  have himpossible :
      (n : ℕ∞) = (n + 1 : ℕ∞) + analyticOrderAt q s := by
    calc
      (n : ℕ∞) =
          analyticOrderAt
            (fun z : ℂ => (z - 1) * deriv zetaPoleRemoved z) s :=
        hleftOrder.symm
      _ = analyticOrderAt
            (fun z : ℂ => zetaPoleRemoved z * q z) s :=
        horders
      _ = (n + 1 : ℕ∞) + analyticOrderAt q s :=
        hrightOrder
  generalize hqorder : analyticOrderAt q s = k at himpossible
  cases k with
  | top =>
      simp at himpossible
  | coe k =>
      norm_cast at himpossible
      omega

/-- A Chebyshev error exponent `r` excludes every nontrivial zeta zero to the right of `r`. -/
theorem nontrivialZero_re_le_of_chebyshevPsiError_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    rho.re ≤ r := by
  by_contra hle
  have hright : r < rho.re := lt_of_not_ge hle
  apply
    zetaPoleRemoved_ne_zero_of_chebyshevPsiError_isBigO
      hO hr0 hr1 hright
  rw [zetaPoleRemoved_eq hrho.2.2]
  exact mul_eq_zero_of_right _ hrho.1

/-- The reverse Chebyshev--von Koch implication: the source error estimate for every positive
epsilon implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_chebyshevPsiError_isBigO
    (hO : ∀ epsilon : ℝ, 0 < epsilon →
      (fun n : ℕ =>
        (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          fun n => (n : ℝ) ^ (1 / 2 + epsilon)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  have hupper :
      ∀ z : ℂ, IsNontrivialZero z → z.re ≤ 1 / 2 := by
    intro z hz
    by_contra hle
    have hzHalf : 1 / 2 < z.re := lt_of_not_ge hle
    let epsilon : ℝ := (z.re - 1 / 2) / 2
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      linarith
    have hr0 : 0 ≤ 1 / 2 + epsilon := by
      linarith
    have hr1 : 1 / 2 + epsilon < 1 := by
      have hzOne := nontrivial_zero_re_lt_one hz
      dsimp only [epsilon]
      linarith
    have hzRight : 1 / 2 + epsilon < z.re := by
      dsimp only [epsilon]
      linarith
    have hzBound :=
      nontrivialZero_re_le_of_chebyshevPsiError_isBigO
        (hO epsilon hepsilon) hr0 hr1 hz
    linarith
  intro rho hrho
  rw [OnCriticalLine]
  have hrhoUpper := hupper rho hrho
  have hreflectUpper :=
    hupper (1 - rho) (isNontrivialZero_one_sub hrho)
  simp only [Complex.sub_re, Complex.one_re] at hreflectUpper
  linarith

/-- A single exponent above one half only confines a reflection-symmetric real part to a band;
it does not force the critical line. -/
theorem fixed_three_quarters_symmetric_band_not_critical :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      beta ≤ 3 / 4 ∧ 1 - beta ≤ 3 / 4 ∧
      beta ≠ 1 / 2 := by
  refine ⟨3 / 4, ?_⟩
  norm_num

/-- Aggregate certificate for the complete conditional reverse von Koch implication. -/
structure ChebyshevReverseZeroExclusionCertificate : Prop where
  mellinDifferentiable :
    ∀ {r : ℝ},
      (fun n : ℕ =>
        (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          (fun n => (n : ℝ) ^ r) →
      0 ≤ r → ∀ {s : ℂ}, r < s.re →
      DifferentiableAt ℂ chebyshevPsiErrorContinuation s
  commonIdentity :
    ∀ {s : ℂ}, 1 < s.re →
      chebyshevPsiErrorContinuation s =
        LSeries chebyshevPsiErrorCoeff s
  poleRemovedODE :
    ∀ {r : ℝ},
      (fun n : ℕ =>
        (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          (fun n => (n : ℝ) ^ r) →
      0 ≤ r → r < 1 → ∀ {s : ℂ}, r < s.re →
      (s - 1) * deriv zetaPoleRemoved s =
        zetaPoleRemoved s *
          (1 - (s - 1) * chebyshevPsiErrorContinuation s -
            zetaPoleRemoved s)
  zeroFree :
    ∀ {r : ℝ},
      (fun n : ℕ =>
        (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          (fun n => (n : ℝ) ^ r) →
      0 ≤ r → r < 1 → ∀ {s : ℂ}, r < s.re →
      zetaPoleRemoved s ≠ 0
  zeroBound :
    ∀ {r : ℝ},
      (fun n : ℕ =>
        (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          (fun n => (n : ℝ) ^ r) →
      0 ≤ r → r < 1 → ∀ {rho : ℂ}, IsNontrivialZero rho →
      rho.re ≤ r
  rhImplication :
    (∀ epsilon : ℝ, 0 < epsilon →
      (fun n : ℕ =>
        (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          fun n => (n : ℝ) ^ (1 / 2 + epsilon)) →
      RiemannHypothesis
  fixedExponentBoundary :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      beta ≤ 3 / 4 ∧ 1 - beta ≤ 3 / 4 ∧
      beta ≠ 1 / 2

theorem chebyshevReverseZeroExclusion_endpoint :
    ChebyshevReverseZeroExclusionCertificate where
  mellinDifferentiable :=
    differentiableAt_chebyshevPsiErrorContinuation_of_isBigO
  commonIdentity := chebyshevPsiErrorContinuation_eq_LSeries
  poleRemovedODE := chebyshevPoleRemovedODE_of_isBigO
  zeroFree :=
    zetaPoleRemoved_ne_zero_of_chebyshevPsiError_isBigO
  zeroBound :=
    nontrivialZero_re_le_of_chebyshevPsiError_isBigO
  rhImplication :=
    riemannHypothesis_of_chebyshevPsiError_isBigO
  fixedExponentBoundary :=
    fixed_three_quarters_symmetric_band_not_critical

end

end LeanLab.Riemann
