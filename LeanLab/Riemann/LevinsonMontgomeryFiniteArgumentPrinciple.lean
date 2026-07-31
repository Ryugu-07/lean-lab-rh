import LeanLab.Riemann.LevinsonMontgomeryNegativeHeightGeometry
import LeanLab.Riemann.WeilZeroCutoff
import Mathlib.Analysis.Meromorphic.FactorizedRational

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A finite analytic rectangle argument principle

This file reconstructs the finite argument principle needed by the Levinson--Montgomery contour.
It extracts the finite divisor into a factorized rational function, promotes the codiscrete
factorization to an equality on the connected analytic domain, and integrates the resulting
finite sum of multiplicity-bearing Cauchy kernels.
-/

namespace LeanLab.Riemann

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators Interval Topology

noncomputable section

/-- On a connected analytic domain, Mathlib's codiscrete finite-divisor extraction is an actual
pointwise factorization. -/
theorem AnalyticOnNhd.extract_zeros_eqOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hUOpen : IsOpen U) (hUPre : IsPreconnected U)
    (horder : ∀ u : U, meromorphicOrderAt f u ≠ ⊤)
    (hfinite : (MeromorphicOn.divisor f U).support.Finite)
    {z0 : ℂ} (hz0 : z0 ∈ U) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ u : U, g u ≠ 0) ∧
      Set.EqOn f
        (fun z => (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f U u)) * g z) U := by
  let D := MeromorphicOn.divisor f U
  let phi : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  obtain ⟨g, hg, hgne, heq⟩ :=
    hf.meromorphicOn.extract_zeros_poles horder hfinite
  have hphiAt : ∀ z : ℂ, AnalyticAt ℂ phi z := by
    intro z
    exact Function.FactorizedRational.analyticAt
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)
  have hproduct :
      AnalyticOnNhd ℂ (fun z => phi z * g z) U := by
    intro z hz
    exact (hphiAt z).mul (hg z hz)
  have heqSet :
      {z | f z = phi z * g z} ∈ codiscreteWithin U := by
    change ∀ᶠ z in codiscreteWithin U, f z = phi z * g z
    filter_upwards [heq] with z hz
    simpa only [phi, D, Pi.smul_apply', smul_eq_mul] using hz
  have hpuncGood :
      {z | f z = phi z * g z} ∪ Uᶜ ∈ 𝓝[≠] z0 :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp heqSet) z0 hz0
  have hpuncU : U ∈ 𝓝[≠] z0 :=
    mem_nhdsWithin_of_mem_nhds (hUOpen.mem_nhds hz0)
  have heqLocal :
      ∀ᶠ z in 𝓝[≠] z0, f z = phi z * g z := by
    filter_upwards [hpuncGood, hpuncU] with z hzGood hzU
    exact hzGood.resolve_right (by simpa using hzU)
  have heqOn :
      Set.EqOn f (fun z => phi z * g z) U :=
    hf.eqOn_of_preconnected_of_frequently_eq
      hproduct hUPre hz0 heqLocal.frequently
  refine ⟨g, hg, hgne, ?_⟩
  simpa only [phi, D, Function.FactorizedRational.finprod_eq_fun hfinite] using heqOn

/-- Extract the finite divisor on a larger set, then promote the codiscrete factorization to an
actual equality on a connected open subset. This separates compact finite support from the open
domain needed by the identity theorem. -/
theorem AnalyticOnNhd.extract_zeros_eqOn_openSubset
    {f : ℂ → ℂ} {K V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    (horder : ∀ u : K, meromorphicOrderAt f u ≠ ⊤)
    (hfinite : (MeromorphicOn.divisor f K).support.Finite)
    {z0 : ℂ} (hz0 : z0 ∈ V) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g K ∧ (∀ u : K, g u ≠ 0) ∧
      Set.EqOn f
        (fun z => (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f K u)) * g z) V := by
  let D := MeromorphicOn.divisor f K
  let phi : ℂ → ℂ := ∏ᶠ u, (fun z : ℂ => z - u) ^ D u
  obtain ⟨g, hg, hgne, heq⟩ :=
    hf.meromorphicOn.extract_zeros_poles horder hfinite
  have hphiAt : ∀ z : ℂ, AnalyticAt ℂ phi z := by
    intro z
    exact Function.FactorizedRational.analyticAt
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)
  have hproduct :
      AnalyticOnNhd ℂ (fun z => phi z * g z) V := by
    intro z hz
    exact (hphiAt z).mul (hg z (hVK hz))
  have heqSet :
      {z | f z = phi z * g z} ∈ codiscreteWithin K := by
    change ∀ᶠ z in codiscreteWithin K, f z = phi z * g z
    filter_upwards [heq] with z hz
    simpa only [phi, D, Pi.smul_apply', smul_eq_mul] using hz
  have hpuncGood :
      {z | f z = phi z * g z} ∪ Kᶜ ∈ 𝓝[≠] z0 :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp heqSet) z0 (hVK hz0)
  have hpuncV : V ∈ 𝓝[≠] z0 :=
    mem_nhdsWithin_of_mem_nhds (hVOpen.mem_nhds hz0)
  have heqLocal :
      ∀ᶠ z in 𝓝[≠] z0, f z = phi z * g z := by
    filter_upwards [hpuncGood, hpuncV] with z hzGood hzV
    exact hzGood.resolve_right (by simpa using hVK hzV)
  have heqOn :
      Set.EqOn f (fun z => phi z * g z) V :=
    (hf.mono hVK).eqOn_of_preconnected_of_frequently_eq
      hproduct hVPre hz0 heqLocal.frequently
  refine ⟨g, hg, hgne, ?_⟩
  simpa only [phi, D, Function.FactorizedRational.finprod_eq_fun hfinite] using heqOn

/-- Away from the finite divisor support, the logarithmic derivative of the factorized rational
function is the finite multiplicity-bearing Cauchy-kernel sum. -/
theorem logDeriv_factorizedRational_eq_divisor_sum
    {D : ℂ → ℤ} (hfinite : D.support.Finite) {z : ℂ}
    (hz : ∀ u ∈ hfinite.toFinset, z ≠ u) :
    logDeriv (∏ᶠ u, (· - u) ^ D u) z =
      ∑ u ∈ hfinite.toFinset, (D u : ℂ) / (z - u) := by
  have hsupport :
      (fun u : ℂ => (· - u) ^ D u).mulSupport ⊆ hfinite.toFinset := by
    intro u hu
    rw [Function.FactorizedRational.mulSupport] at hu
    simpa using hu
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupport]
  have hfun :
      (∏ u ∈ hfinite.toFinset, (fun x : ℂ => x - u) ^ D u) =
        (fun x : ℂ => ∏ u ∈ hfinite.toFinset, (x - u) ^ D u) := by
    ext x
    simp
  rw [hfun]
  have hprod :
      logDeriv (fun x : ℂ =>
        ∏ u ∈ hfinite.toFinset, (x - u) ^ D u) z =
        ∑ u ∈ hfinite.toFinset,
          logDeriv (fun w : ℂ => (w - u) ^ D u) z := by
    apply logDeriv_prod
    · intro u hu
      exact zpow_ne_zero (D u) (sub_ne_zero.mpr (hz u hu))
    · intro u hu
      exact DifferentiableAt.zpow (by fun_prop) (Or.inl (sub_ne_zero.mpr (hz u hu)))
  rw [hprod]
  apply Finset.sum_congr rfl
  intro u hu
  rw [logDeriv_fun_zpow (by fun_prop) (D u)]
  have hbase :
      logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) := by
    rw [logDeriv_apply]
    simp
  rw [hbase]
  ring

/-- Rectangle boundary integration commutes with a finite sum when every summand is integrable
on every edge. -/
theorem rectangleBoundaryIntegral_finset_sum
    {ι : Type*} {s : Finset ι} {F : ι → ℂ → ℂ}
    {l r b t : ℝ}
    (hb : ∀ i ∈ s,
      IntervalIntegrable (fun x : ℝ => F i (x + b * I)) volume l r)
    (ht : ∀ i ∈ s,
      IntervalIntegrable (fun x : ℝ => F i (x + t * I)) volume l r)
    (hr : ∀ i ∈ s,
      IntervalIntegrable (fun y : ℝ => F i (r + y * I)) volume b t)
    (hl : ∀ i ∈ s,
      IntervalIntegrable (fun y : ℝ => F i (l + y * I)) volume b t) :
    rectangleBoundaryIntegral (fun z => ∑ i ∈ s, F i z) l r b t =
      ∑ i ∈ s, rectangleBoundaryIntegral (F i) l r b t := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_finsetSum hb,
    intervalIntegral.integral_finsetSum ht,
    intervalIntegral.integral_finsetSum hr,
    intervalIntegral.integral_finsetSum hl]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A complex point lies strictly inside the rectangle with the displayed orientation. -/
def pointStrictlyInsideRectangle (l r b t : ℝ) (z : ℂ) : Prop :=
  l < z.re ∧ z.re < r ∧ b < z.im ∧ z.im < t

instance decidablePointStrictlyInsideRectangle (l r b t : ℝ) (z : ℂ) :
    Decidable (pointStrictlyInsideRectangle l r b t z) := by
  unfold pointStrictlyInsideRectangle
  infer_instance

/-- A finite multiplicity-bearing Cauchy-kernel sum counts exactly the support points strictly
inside a rectangle. The explicit edge-avoidance hypotheses prevent any endpoint convention from
being hidden in the integral. -/
theorem rectangleBoundaryIntegral_divisorKernel_sum
    {D : ℂ → ℤ} {s : Finset ℂ} {l r b t : ℝ}
    (hbottom : ∀ u ∈ s, ∀ x ∈ [[l, r]], (x : ℂ) + b * I ≠ u)
    (htop : ∀ u ∈ s, ∀ x ∈ [[l, r]], (x : ℂ) + t * I ≠ u)
    (hright : ∀ u ∈ s, ∀ y ∈ [[b, t]], (r : ℂ) + y * I ≠ u)
    (hleft : ∀ u ∈ s, ∀ y ∈ [[b, t]], (l : ℂ) + y * I ≠ u)
    (hposition : ∀ u ∈ s,
      pointStrictlyInsideRectangle l r b t u ∨
        (u.re ∉ [[l, r]] ∨ u.im ∉ [[b, t]])) :
    rectangleBoundaryIntegral
        (fun z => ∑ u ∈ s, (D u : ℂ) / (z - u)) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ s.filter (pointStrictlyInsideRectangle l r b t), (D u : ℂ) := by
  classical
  have hbInt : ∀ u ∈ s,
      IntervalIntegrable
        (fun x : ℝ => (D u : ℂ) / ((x : ℂ) + b * I - u)) volume l r := by
    intro u hu
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids
      (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
    exact hbottom u hu
  have htInt : ∀ u ∈ s,
      IntervalIntegrable
        (fun x : ℝ => (D u : ℂ) / ((x : ℂ) + t * I - u)) volume l r := by
    intro u hu
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids
      (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
    exact htop u hu
  have hrInt : ∀ u ∈ s,
      IntervalIntegrable
        (fun y : ℝ => (D u : ℂ) / ((r : ℂ) + y * I - u)) volume b t := by
    intro u hu
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids
      (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
    exact hright u hu
  have hlInt : ∀ u ∈ s,
      IntervalIntegrable
        (fun y : ℝ => (D u : ℂ) / ((l : ℂ) + y * I - u)) volume b t := by
    intro u hu
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids
      (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
    exact hleft u hu
  rw [rectangleBoundaryIntegral_finset_sum hbInt htInt hrInt hlInt]
  have hterm : ∀ u ∈ s,
      rectangleBoundaryIntegral (fun z => (D u : ℂ) / (z - u)) l r b t =
        if pointStrictlyInsideRectangle l r b t u then
          2 * (Real.pi : ℂ) * I * (D u : ℂ)
        else 0 := by
    intro u hu
    by_cases hin : pointStrictlyInsideRectangle l r b t u
    · rw [if_pos hin]
      exact rectangleBoundaryIntegral_weighted_cauchyKernel
        (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop)
          hin.1 hin.2.1 hin.2.2.1 hin.2.2.2
    · rw [if_neg hin]
      rcases hposition u hu with hinside | houtside
      · exact (hin hinside).elim
      · exact rectangleBoundaryIntegral_weighted_cauchyKernel_eq_zero_of_outside
          (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) houtside
  calc
    ∑ u ∈ s, rectangleBoundaryIntegral
        (fun z => (D u : ℂ) / (z - u)) l r b t =
        ∑ u ∈ s, if pointStrictlyInsideRectangle l r b t u then
          2 * (Real.pi : ℂ) * I * (D u : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hterm u hu
    _ = 2 * (Real.pi : ℂ) * I *
        ∑ u ∈ s.filter (pointStrictlyInsideRectangle l r b t), (D u : ℂ) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_filter]

/-- On an analytic factorization into a finite zero factor and a nonvanishing factor, the
logarithmic derivative is the corresponding divisor-kernel sum plus the residual logarithmic
derivative. -/
theorem logDeriv_eq_divisor_sum_add_logDeriv_of_factorization
    {f g : ℂ → ℂ} {D : ℂ → ℤ} {U : Set ℂ}
    (hUOpen : IsOpen U) (hfinite : D.support.Finite)
    (hDnonneg : ∀ u, 0 ≤ D u)
    (hg : AnalyticOnNhd ℂ g U) (hgne : ∀ u : U, g u ≠ 0)
    (heq : Set.EqOn f
      (fun w => (∏ᶠ u, (w - u) ^ D u) * g w) U)
    {z : ℂ} (hzU : z ∈ U) (hfne : f z ≠ 0)
    (hz : ∀ u ∈ hfinite.toFinset, z ≠ u) :
    logDeriv f z =
      ∑ u ∈ hfinite.toFinset, (D u : ℂ) / (z - u) + logDeriv g z := by
  let phi : ℂ → ℂ := fun w => ∏ᶠ u, (w - u) ^ D u
  have hphiEq :
      (∏ᶠ u, (fun w : ℂ => w - u) ^ D u) = phi := by
    simpa only [phi] using Function.FactorizedRational.finprod_eq_fun hfinite
  have hphiNe : phi z ≠ 0 := by
    intro hzero
    apply hfne
    rw [heq hzU]
    simp only [phi, hzero, zero_mul]
  have hphiDiff : DifferentiableAt ℂ phi z := by
    rw [← hphiEq]
    exact (Function.FactorizedRational.analyticAt (hDnonneg z)).differentiableAt
  have hgDiff : DifferentiableAt ℂ g z :=
    (hg z hzU).differentiableAt
  have hlogEq :
      logDeriv f z = logDeriv (fun w => phi w * g w) z := by
    rw [logDeriv_apply, logDeriv_apply]
    apply congrArg₂ (fun a b : ℂ => a / b)
    · exact heq.deriv hUOpen hzU
    · simpa only [phi, Pi.smul_apply', smul_eq_mul] using heq hzU
  rw [hlogEq, logDeriv_mul z hphiNe (hgne ⟨z, hzU⟩) hphiDiff hgDiff,
    ← hphiEq, logDeriv_factorizedRational_eq_divisor_sum hfinite hz]

/-- Finite analytic argument principle on a rectangle, stated for an explicit zero-factorization.
Every boundary-avoidance and inside/outside decision is exposed as a hypothesis. -/
theorem rectangleBoundaryIntegral_logDeriv_eq_divisor_sum_of_factorization
    {f g : ℂ → ℂ} {D : ℂ → ℤ} {U : Set ℂ}
    {l r b t : ℝ}
    (hUOpen : IsOpen U) (hfinite : D.support.Finite)
    (hDnonneg : ∀ u, 0 ≤ D u)
    (hg : AnalyticOnNhd ℂ g U) (hgne : ∀ u : U, g u ≠ 0)
    (heq : Set.EqOn f
      (fun w => (∏ᶠ u, (w - u) ^ D u) * g w) U)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ U)
    (hfBottom : ∀ x ∈ [[l, r]], f ((x : ℂ) + b * I) ≠ 0)
    (hfTop : ∀ x ∈ [[l, r]], f ((x : ℂ) + t * I) ≠ 0)
    (hfRight : ∀ y ∈ [[b, t]], f ((r : ℂ) + y * I) ≠ 0)
    (hfLeft : ∀ y ∈ [[b, t]], f ((l : ℂ) + y * I) ≠ 0)
    (hbottom : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + b * I ≠ u)
    (htop : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + t * I ≠ u)
    (hright : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (r : ℂ) + y * I ≠ u)
    (hleft : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (l : ℂ) + y * I ≠ u)
    (hposition : ∀ u ∈ hfinite.toFinset,
      pointStrictlyInsideRectangle l r b t u ∨
        (u.re ∉ [[l, r]] ∨ u.im ∉ [[b, t]])) :
    rectangleBoundaryIntegral (logDeriv f) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ hfinite.toFinset.filter (pointStrictlyInsideRectangle l r b t),
          (D u : ℂ) := by
  let K : ℂ → ℂ := fun z =>
    ∑ u ∈ hfinite.toFinset, (D u : ℂ) / (z - u)
  have hbottomMap : MapsTo (fun x : ℝ => (x : ℂ) + b * I) [[l, r]] U := by
    intro x hx
    apply hrect
    constructor
    · simpa using hx
    · simp
  have htopMap : MapsTo (fun x : ℝ => (x : ℂ) + t * I) [[l, r]] U := by
    intro x hx
    apply hrect
    constructor
    · simpa using hx
    · simp
  have hrightMap : MapsTo (fun y : ℝ => (r : ℂ) + y * I) [[b, t]] U := by
    intro y hy
    apply hrect
    constructor
    · simp
    · simpa using hy
  have hleftMap : MapsTo (fun y : ℝ => (l : ℂ) + y * I) [[b, t]] U := by
    intro y hy
    apply hrect
    constructor
    · simp
    · simpa using hy
  have hbottomEq : ∀ x ∈ [[l, r]],
      logDeriv f ((x : ℂ) + b * I) =
        K ((x : ℂ) + b * I) + logDeriv g ((x : ℂ) + b * I) := by
    intro x hx
    exact logDeriv_eq_divisor_sum_add_logDeriv_of_factorization
      hUOpen hfinite hDnonneg hg hgne heq (hbottomMap hx) (hfBottom x hx)
        (fun u hu => hbottom u hu x hx)
  have htopEq : ∀ x ∈ [[l, r]],
      logDeriv f ((x : ℂ) + t * I) =
        K ((x : ℂ) + t * I) + logDeriv g ((x : ℂ) + t * I) := by
    intro x hx
    exact logDeriv_eq_divisor_sum_add_logDeriv_of_factorization
      hUOpen hfinite hDnonneg hg hgne heq (htopMap hx) (hfTop x hx)
        (fun u hu => htop u hu x hx)
  have hrightEq : ∀ y ∈ [[b, t]],
      logDeriv f ((r : ℂ) + y * I) =
        K ((r : ℂ) + y * I) + logDeriv g ((r : ℂ) + y * I) := by
    intro y hy
    exact logDeriv_eq_divisor_sum_add_logDeriv_of_factorization
      hUOpen hfinite hDnonneg hg hgne heq (hrightMap hy) (hfRight y hy)
        (fun u hu => hright u hu y hy)
  have hleftEq : ∀ y ∈ [[b, t]],
      logDeriv f ((l : ℂ) + y * I) =
        K ((l : ℂ) + y * I) + logDeriv g ((l : ℂ) + y * I) := by
    intro y hy
    exact logDeriv_eq_divisor_sum_add_logDeriv_of_factorization
      hUOpen hfinite hDnonneg hg hgne heq (hleftMap hy) (hfLeft y hy)
        (fun u hu => hleft u hu y hy)
  have hdecomp :
      rectangleBoundaryIntegral (logDeriv f) l r b t =
        rectangleBoundaryIntegral (fun z => K z + logDeriv g z) l r b t := by
    have hbEq := intervalIntegral.integral_congr (μ := volume) hbottomEq
    have htEq := intervalIntegral.integral_congr (μ := volume) htopEq
    have hrEq := intervalIntegral.integral_congr (μ := volume) hrightEq
    have hlEq := intervalIntegral.integral_congr (μ := volume) hleftEq
    unfold rectangleBoundaryIntegral
    rw [hbEq, htEq, hrEq, hlEq]
  have hKBottom : IntervalIntegrable
      (fun x : ℝ => K ((x : ℂ) + b * I)) volume l r := by
    have hterms : ∀ u ∈ hfinite.toFinset, IntervalIntegrable
        (fun x : ℝ => (D u : ℂ) / ((x : ℂ) + b * I - u)) volume l r := by
      intro u hu
      apply intervalIntegrable_weighted_cauchyKernel_of_avoids
        (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
      exact hbottom u hu
    have hfun :
        (∑ u ∈ hfinite.toFinset,
          fun x : ℝ => (D u : ℂ) / ((x : ℂ) + b * I - u)) =
          (fun x : ℝ => K ((x : ℂ) + b * I)) := by
      ext x
      simp only [K, Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum hfinite.toFinset hterms
  have hKTop : IntervalIntegrable
      (fun x : ℝ => K ((x : ℂ) + t * I)) volume l r := by
    have hterms : ∀ u ∈ hfinite.toFinset, IntervalIntegrable
        (fun x : ℝ => (D u : ℂ) / ((x : ℂ) + t * I - u)) volume l r := by
      intro u hu
      apply intervalIntegrable_weighted_cauchyKernel_of_avoids
        (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
      exact htop u hu
    have hfun :
        (∑ u ∈ hfinite.toFinset,
          fun x : ℝ => (D u : ℂ) / ((x : ℂ) + t * I - u)) =
          (fun x : ℝ => K ((x : ℂ) + t * I)) := by
      ext x
      simp only [K, Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum hfinite.toFinset hterms
  have hKRight : IntervalIntegrable
      (fun y : ℝ => K ((r : ℂ) + y * I)) volume b t := by
    have hterms : ∀ u ∈ hfinite.toFinset, IntervalIntegrable
        (fun y : ℝ => (D u : ℂ) / ((r : ℂ) + y * I - u)) volume b t := by
      intro u hu
      apply intervalIntegrable_weighted_cauchyKernel_of_avoids
        (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
      exact hright u hu
    have hfun :
        (∑ u ∈ hfinite.toFinset,
          fun y : ℝ => (D u : ℂ) / ((r : ℂ) + y * I - u)) =
          (fun y : ℝ => K ((r : ℂ) + y * I)) := by
      ext y
      simp only [K, Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum hfinite.toFinset hterms
  have hKLeft : IntervalIntegrable
      (fun y : ℝ => K ((l : ℂ) + y * I)) volume b t := by
    have hterms : ∀ u ∈ hfinite.toFinset, IntervalIntegrable
        (fun y : ℝ => (D u : ℂ) / ((l : ℂ) + y * I - u)) volume b t := by
      intro u hu
      apply intervalIntegrable_weighted_cauchyKernel_of_avoids
        (F := fun _ : ℂ => (D u : ℂ)) (by fun_prop) (by fun_prop)
      exact hleft u hu
    have hfun :
        (∑ u ∈ hfinite.toFinset,
          fun y : ℝ => (D u : ℂ) / ((l : ℂ) + y * I - u)) =
          (fun y : ℝ => K ((l : ℂ) + y * I)) := by
      ext y
      simp only [K, Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum hfinite.toFinset hterms
  have hlogg : AnalyticOnNhd ℂ (logDeriv g) U := by
    intro z hz
    change AnalyticAt ℂ (fun w => deriv g w / g w) z
    exact (hg.deriv z hz).div (hg z hz) (hgne ⟨z, hz⟩)
  have hgBottom : IntervalIntegrable
      (fun x : ℝ => logDeriv g ((x : ℂ) + b * I)) volume l r :=
    intervalIntegrable_comp_of_differentiableOn hUOpen hlogg.differentiableOn
      (by fun_prop) hbottomMap
  have hgTop : IntervalIntegrable
      (fun x : ℝ => logDeriv g ((x : ℂ) + t * I)) volume l r :=
    intervalIntegrable_comp_of_differentiableOn hUOpen hlogg.differentiableOn
      (by fun_prop) htopMap
  have hgRight : IntervalIntegrable
      (fun y : ℝ => logDeriv g ((r : ℂ) + y * I)) volume b t :=
    intervalIntegrable_comp_of_differentiableOn hUOpen hlogg.differentiableOn
      (by fun_prop) hrightMap
  have hgLeft : IntervalIntegrable
      (fun y : ℝ => logDeriv g ((l : ℂ) + y * I)) volume b t :=
    intervalIntegrable_comp_of_differentiableOn hUOpen hlogg.differentiableOn
      (by fun_prop) hleftMap
  have hadd := rectangleBoundaryIntegral_add
    hKBottom hgBottom hKTop hgTop hKRight hgRight hKLeft hgLeft
  have hgZero : rectangleBoundaryIntegral (logDeriv g) l r b t = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn
      (hlogg.differentiableOn.mono hrect)
  calc
    rectangleBoundaryIntegral (logDeriv f) l r b t =
        rectangleBoundaryIntegral (fun z => K z + logDeriv g z) l r b t := hdecomp
    _ = rectangleBoundaryIntegral K l r b t +
        rectangleBoundaryIntegral (logDeriv g) l r b t := hadd
    _ = rectangleBoundaryIntegral K l r b t := by rw [hgZero, add_zero]
    _ = 2 * (Real.pi : ℂ) * I *
        ∑ u ∈ hfinite.toFinset.filter (pointStrictlyInsideRectangle l r b t),
          (D u : ℂ) := by
      exact rectangleBoundaryIntegral_divisorKernel_sum
        hbottom htop hright hleft hposition

/-- Finite analytic argument principle on a rectangle, expressed directly through Mathlib's
analytic divisor. -/
theorem finite_analytic_rectangle_argumentPrinciple
    {f : ℂ → ℂ} {U : Set ℂ} {l r b t : ℝ}
    (hf : AnalyticOnNhd ℂ f U) (hUOpen : IsOpen U) (hUPre : IsPreconnected U)
    (horder : ∀ u : U, meromorphicOrderAt f u ≠ ⊤)
    (hfinite : (MeromorphicOn.divisor f U).support.Finite)
    {z0 : ℂ} (hz0 : z0 ∈ U)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ U)
    (hfBottom : ∀ x ∈ [[l, r]], f ((x : ℂ) + b * I) ≠ 0)
    (hfTop : ∀ x ∈ [[l, r]], f ((x : ℂ) + t * I) ≠ 0)
    (hfRight : ∀ y ∈ [[b, t]], f ((r : ℂ) + y * I) ≠ 0)
    (hfLeft : ∀ y ∈ [[b, t]], f ((l : ℂ) + y * I) ≠ 0)
    (hbottom : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + b * I ≠ u)
    (htop : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + t * I ≠ u)
    (hright : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (r : ℂ) + y * I ≠ u)
    (hleft : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (l : ℂ) + y * I ≠ u)
    (hposition : ∀ u ∈ hfinite.toFinset,
      pointStrictlyInsideRectangle l r b t u ∨
        (u.re ∉ [[l, r]] ∨ u.im ∉ [[b, t]])) :
    rectangleBoundaryIntegral (logDeriv f) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ hfinite.toFinset.filter (pointStrictlyInsideRectangle l r b t),
          (MeromorphicOn.divisor f U u : ℂ) := by
  obtain ⟨g, hg, hgne, heq⟩ :=
    AnalyticOnNhd.extract_zeros_eqOn hf hUOpen hUPre horder hfinite hz0
  exact rectangleBoundaryIntegral_logDeriv_eq_divisor_sum_of_factorization
    hUOpen hfinite (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)
      hg hgne heq hrect hfBottom hfTop hfRight hfLeft
        hbottom htop hright hleft hposition

/-- Usable finite analytic argument principle: the divisor is cut off on a larger set `K`, while
factorization and contour integration occur on an open connected subset `V`. -/
theorem finite_analytic_rectangle_argumentPrinciple_of_openSubset
    {f : ℂ → ℂ} {K V : Set ℂ} {l r b t : ℝ}
    (hf : AnalyticOnNhd ℂ f K)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    (horder : ∀ u : K, meromorphicOrderAt f u ≠ ⊤)
    (hfinite : (MeromorphicOn.divisor f K).support.Finite)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ V)
    (hfBottom : ∀ x ∈ [[l, r]], f ((x : ℂ) + b * I) ≠ 0)
    (hfTop : ∀ x ∈ [[l, r]], f ((x : ℂ) + t * I) ≠ 0)
    (hfRight : ∀ y ∈ [[b, t]], f ((r : ℂ) + y * I) ≠ 0)
    (hfLeft : ∀ y ∈ [[b, t]], f ((l : ℂ) + y * I) ≠ 0)
    (hbottom : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + b * I ≠ u)
    (htop : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + t * I ≠ u)
    (hright : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (r : ℂ) + y * I ≠ u)
    (hleft : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (l : ℂ) + y * I ≠ u)
    (hposition : ∀ u ∈ hfinite.toFinset,
      pointStrictlyInsideRectangle l r b t u ∨
        (u.re ∉ [[l, r]] ∨ u.im ∉ [[b, t]])) :
    rectangleBoundaryIntegral (logDeriv f) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ hfinite.toFinset.filter (pointStrictlyInsideRectangle l r b t),
          (MeromorphicOn.divisor f K u : ℂ) := by
  obtain ⟨g, hg, hgne, heq⟩ :=
    AnalyticOnNhd.extract_zeros_eqOn_openSubset
      hf hVOpen hVPre hVK horder hfinite hz0
  exact rectangleBoundaryIntegral_logDeriv_eq_divisor_sum_of_factorization
    hVOpen hfinite (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)
      (hg.mono hVK) (fun u => hgne ⟨u, hVK u.property⟩) heq
        hrect hfBottom hfTop hfRight hfLeft hbottom htop hright hleft hposition

/-- Every support point of an analytic divisor is an actual zero. -/
theorem eq_zero_of_mem_analytic_divisor_support
    {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    {z : ℂ} (hz : z ∈ (MeromorphicOn.divisor f K).support) :
    f z = 0 := by
  have hzK : z ∈ K := (MeromorphicOn.divisor f K).supportWithinDomain hz
  have hdivNe : MeromorphicOn.divisor f K z ≠ 0 := by
    simpa only [Function.mem_support] using hz
  apply apply_eq_zero_of_analyticOrderAt_ne_zero
  intro horder
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, horder] at hdivNe
  simp at hdivNe

/-- Conversely, a zero of finite local order in the analytic domain belongs to the divisor
support. -/
theorem mem_analytic_divisor_support_of_eq_zero
    {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    (horder : ∀ u : K, meromorphicOrderAt f u ≠ ⊤)
    {z : ℂ} (hzK : z ∈ K) (hzero : f z = 0) :
    z ∈ (MeromorphicOn.divisor f K).support := by
  rw [Function.mem_support, MeromorphicOn.divisor_apply hf.meromorphicOn hzK]
  intro huntop
  rw [WithTop.untop₀_eq_zero] at huntop
  rcases huntop with hmerZero | hmerTop
  · rw [(hf z hzK).meromorphicOrderAt_eq] at hmerZero
    have horderZero : analyticOrderAt f z = 0 := by
      simpa using hmerZero
    exact (hf z hzK).analyticOrderAt_ne_zero.mpr hzero horderZero
  · exact horder ⟨z, hzK⟩ hmerTop

/-- A point avoiding all four edges of a nondegenerate rectangle is either strictly inside or
outside the closed rectangle in at least one coordinate. -/
theorem pointStrictlyInside_or_outside_of_avoids_boundary
    {u : ℂ} {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hbottom : ∀ x ∈ [[l, r]], (x : ℂ) + b * I ≠ u)
    (htop : ∀ x ∈ [[l, r]], (x : ℂ) + t * I ≠ u)
    (hright : ∀ y ∈ [[b, t]], (r : ℂ) + y * I ≠ u)
    (hleft : ∀ y ∈ [[b, t]], (l : ℂ) + y * I ≠ u) :
    pointStrictlyInsideRectangle l r b t u ∨
      (u.re ∉ [[l, r]] ∨ u.im ∉ [[b, t]]) := by
  by_cases hre : u.re ∈ [[l, r]]
  · by_cases him : u.im ∈ [[b, t]]
    · left
      have hreIcc : u.re ∈ Set.Icc l r := by
        simpa only [uIcc_of_le hlr.le] using hre
      have himIcc : u.im ∈ Set.Icc b t := by
        simpa only [uIcc_of_le hbt.le] using him
      have hneLeft : u.re ≠ l := by
        intro heq
        apply hleft u.im him
        apply Complex.ext
        · simp [heq]
        · simp
      have hneRight : u.re ≠ r := by
        intro heq
        apply hright u.im him
        apply Complex.ext
        · simp [heq]
        · simp
      have hneBottom : u.im ≠ b := by
        intro heq
        apply hbottom u.re hre
        apply Complex.ext
        · simp
        · simp [heq]
      have hneTop : u.im ≠ t := by
        intro heq
        apply htop u.re hre
        apply Complex.ext
        · simp
        · simp [heq]
      exact ⟨lt_of_le_of_ne hreIcc.1 (Ne.symm hneLeft),
        lt_of_le_of_ne hreIcc.2 hneRight,
        lt_of_le_of_ne himIcc.1 (Ne.symm hneBottom),
        lt_of_le_of_ne himIcc.2 hneTop⟩
    · exact Or.inr (Or.inr him)
  · exact Or.inr (Or.inl hre)

/-- Finite analytic argument principle with edge avoidance and support classification derived from
the single mathematical condition that the function is nonzero on the four boundary edges. -/
theorem finite_analytic_rectangle_argumentPrinciple_of_boundaryNonzero
    {f : ℂ → ℂ} {K V : Set ℂ} {l r b t : ℝ}
    (hf : AnalyticOnNhd ℂ f K)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    (horder : ∀ u : K, meromorphicOrderAt f u ≠ ⊤)
    (hfinite : (MeromorphicOn.divisor f K).support.Finite)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ V)
    (hlr : l < r) (hbt : b < t)
    (hfBottom : ∀ x ∈ [[l, r]], f ((x : ℂ) + b * I) ≠ 0)
    (hfTop : ∀ x ∈ [[l, r]], f ((x : ℂ) + t * I) ≠ 0)
    (hfRight : ∀ y ∈ [[b, t]], f ((r : ℂ) + y * I) ≠ 0)
    (hfLeft : ∀ y ∈ [[b, t]], f ((l : ℂ) + y * I) ≠ 0) :
    rectangleBoundaryIntegral (logDeriv f) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ hfinite.toFinset.filter (pointStrictlyInsideRectangle l r b t),
          (MeromorphicOn.divisor f K u : ℂ) := by
  have hbottom : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + b * I ≠ u := by
    intro u hu x hx heq
    have huSupport : u ∈ (MeromorphicOn.divisor f K).support := by
      simpa using hu
    apply hfBottom x hx
    rw [heq]
    exact eq_zero_of_mem_analytic_divisor_support hf huSupport
  have htop : ∀ u ∈ hfinite.toFinset, ∀ x ∈ [[l, r]],
      (x : ℂ) + t * I ≠ u := by
    intro u hu x hx heq
    have huSupport : u ∈ (MeromorphicOn.divisor f K).support := by
      simpa using hu
    apply hfTop x hx
    rw [heq]
    exact eq_zero_of_mem_analytic_divisor_support hf huSupport
  have hright : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (r : ℂ) + y * I ≠ u := by
    intro u hu y hy heq
    have huSupport : u ∈ (MeromorphicOn.divisor f K).support := by
      simpa using hu
    apply hfRight y hy
    rw [heq]
    exact eq_zero_of_mem_analytic_divisor_support hf huSupport
  have hleft : ∀ u ∈ hfinite.toFinset, ∀ y ∈ [[b, t]],
      (l : ℂ) + y * I ≠ u := by
    intro u hu y hy heq
    have huSupport : u ∈ (MeromorphicOn.divisor f K).support := by
      simpa using hu
    apply hfLeft y hy
    rw [heq]
    exact eq_zero_of_mem_analytic_divisor_support hf huSupport
  have hposition : ∀ u ∈ hfinite.toFinset,
      pointStrictlyInsideRectangle l r b t u ∨
        (u.re ∉ [[l, r]] ∨ u.im ∉ [[b, t]]) := by
    intro u hu
    exact pointStrictlyInside_or_outside_of_avoids_boundary hlr hbt
      (hbottom u hu) (htop u hu) (hright u hu) (hleft u hu)
  exact finite_analytic_rectangle_argumentPrinciple_of_openSubset
    hf hVOpen hVPre hVK horder hfinite hz0 hrect
      hfBottom hfTop hfRight hfLeft hbottom htop hright hleft hposition

/-- The support finset of an analytic divisor cut off on a compact set. -/
noncomputable def compactAnalyticDivisorSupportFinset
    (f : ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K) : Finset ℂ :=
  ((MeromorphicOn.divisor f K).finiteSupport hK).toFinset

@[simp]
theorem mem_compactAnalyticDivisorSupportFinset
    {f : ℂ → ℂ} {K : Set ℂ} {hK : IsCompact K} {z : ℂ} :
    z ∈ compactAnalyticDivisorSupportFinset f K hK ↔
      z ∈ (MeromorphicOn.divisor f K).support := by
  simp [compactAnalyticDivisorSupportFinset]

/-- The analytic order of zeta is finite at every point other than its pole. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_ne_one
    {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hconnected : IsPreconnected (({1} : Set ℂ)ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have horderZero : analyticOrderAt riemannZeta (0 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannZeta_zero]; norm_num))]
    exact ENat.zero_ne_top
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    hconnected (by simp) (by simpa using hs) horderZero

/-- Actual zeta argument principle on any pole-free compact cutoff and any boundary-zero-free
rectangle lying in a connected open subset of that cutoff. -/
theorem riemannZeta_finiteRectangle_argumentPrinciple
    {K V : Set ℂ} {l r b t : ℝ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ V)
    (hlr : l < r) (hbt : b < t)
    (hfBottom : ∀ x ∈ [[l, r]], riemannZeta ((x : ℂ) + b * I) ≠ 0)
    (hfTop : ∀ x ∈ [[l, r]], riemannZeta ((x : ℂ) + t * I) ≠ 0)
    (hfRight : ∀ y ∈ [[b, t]], riemannZeta ((r : ℂ) + y * I) ≠ 0)
    (hfLeft : ∀ y ∈ [[b, t]], riemannZeta ((l : ℂ) + y * I) ≠ 0) :
    rectangleBoundaryIntegral (logDeriv riemannZeta) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
            (pointStrictlyInsideRectangle l r b t),
          (MeromorphicOn.divisor riemannZeta K u : ℂ) := by
  let hfinite := (MeromorphicOn.divisor riemannZeta K).finiteSupport hK
  have hf : AnalyticOnNhd ℂ riemannZeta K :=
    analyticOn_riemannZeta.mono hKDomain
  have horder : ∀ u : K, meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    intro u
    rw [(hf u u.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_riemannZeta_ne_top_of_ne_one (hKDomain u.property)
  have harg := finite_analytic_rectangle_argumentPrinciple_of_boundaryNonzero
    hf hVOpen hVPre hVK horder hfinite hz0 hrect hlr hbt
      hfBottom hfTop hfRight hfLeft
  simpa only [compactAnalyticDivisorSupportFinset, hfinite] using harg

/-- Actual zeta-derivative argument principle on any pole-free compact cutoff and any
boundary-zero-free rectangle lying in a connected open subset of that cutoff. -/
theorem riemannZetaDeriv_finiteRectangle_argumentPrinciple
    {K V : Set ℂ} {l r b t : ℝ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ V)
    (hlr : l < r) (hbt : b < t)
    (hfBottom : ∀ x ∈ [[l, r]], deriv riemannZeta ((x : ℂ) + b * I) ≠ 0)
    (hfTop : ∀ x ∈ [[l, r]], deriv riemannZeta ((x : ℂ) + t * I) ≠ 0)
    (hfRight : ∀ y ∈ [[b, t]], deriv riemannZeta ((r : ℂ) + y * I) ≠ 0)
    (hfLeft : ∀ y ∈ [[b, t]], deriv riemannZeta ((l : ℂ) + y * I) ≠ 0) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ u ∈ (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
            (pointStrictlyInsideRectangle l r b t),
          (MeromorphicOn.divisor (deriv riemannZeta) K u : ℂ) := by
  let hfinite := (MeromorphicOn.divisor (deriv riemannZeta) K).finiteSupport hK
  have hf : AnalyticOnNhd ℂ (deriv riemannZeta) K :=
    analyticOnNhd_deriv_riemannZeta.mono hKDomain
  have horder : ∀ u : K, meromorphicOrderAt (deriv riemannZeta) u ≠ ⊤ := by
    intro u
    rw [(hf u u.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_deriv_riemannZeta_ne_top (hKDomain u.property)
  have harg := finite_analytic_rectangle_argumentPrinciple_of_boundaryNonzero
    hf hVOpen hVPre hVK horder hfinite hz0 hrect hlr hbt
      hfBottom hfTop hfRight hfLeft
  simpa only [compactAnalyticDivisorSupportFinset, hfinite] using harg

/-- The zero-free-boundary baseline of the Levinson--Montgomery count-difference identity. Both
actual divisors retain their analytic multiplicities. Critical-line boundary zeros still require
the separate indentation bookkeeping. -/
theorem levinsonMontgomery_zeroFreeRectangle_countDifference
    {K V : Set ℂ} {l r b t : ℝ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ V)
    (hlr : l < r) (hbt : b < t)
    (hzetaBottom : ∀ x ∈ [[l, r]], riemannZeta ((x : ℂ) + b * I) ≠ 0)
    (hzetaTop : ∀ x ∈ [[l, r]], riemannZeta ((x : ℂ) + t * I) ≠ 0)
    (hzetaRight : ∀ y ∈ [[b, t]], riemannZeta ((r : ℂ) + y * I) ≠ 0)
    (hzetaLeft : ∀ y ∈ [[b, t]], riemannZeta ((l : ℂ) + y * I) ≠ 0)
    (hderivBottom : ∀ x ∈ [[l, r]], deriv riemannZeta ((x : ℂ) + b * I) ≠ 0)
    (hderivTop : ∀ x ∈ [[l, r]], deriv riemannZeta ((x : ℂ) + t * I) ≠ 0)
    (hderivRight : ∀ y ∈ [[b, t]], deriv riemannZeta ((r : ℂ) + y * I) ≠ 0)
    (hderivLeft : ∀ y ∈ [[b, t]], deriv riemannZeta ((l : ℂ) + y * I) ≠ 0) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) l r b t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) l r b t =
      2 * (Real.pi : ℂ) * I *
        ((∑ u ∈
            (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
              (pointStrictlyInsideRectangle l r b t),
            (MeromorphicOn.divisor (deriv riemannZeta) K u : ℂ)) -
          ∑ u ∈
            (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
              (pointStrictlyInsideRectangle l r b t),
            (MeromorphicOn.divisor riemannZeta K u : ℂ)) := by
  have hzeta := riemannZeta_finiteRectangle_argumentPrinciple
    hK hKDomain hVOpen hVPre hVK hz0 hrect hlr hbt
      hzetaBottom hzetaTop hzetaRight hzetaLeft
  have hderiv := riemannZetaDeriv_finiteRectangle_argumentPrinciple
    hK hKDomain hVOpen hVPre hVK hz0 hrect hlr hbt
      hderivBottom hderivTop hderivRight hderivLeft
  rw [hzeta, hderiv]
  ring

/-- A finite family of real parts lying below `c` has a strict common upper bound below `c`. -/
theorem exists_finset_re_strictUpperBound
    {S : Finset ℂ} {c : ℝ} (hS : ∀ z ∈ S, z.re < c) :
    ∃ r : ℝ, r < c ∧ ∀ z ∈ S, z.re < r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨c - 1, by linarith, ?_⟩
      simp
  | @insert a S ha ih =>
      have haC : a.re < c := hS a (by simp)
      have hSC : ∀ z ∈ S, z.re < c := by
        intro z hz
        exact hS z (by simp [hz])
      obtain ⟨r, hrC, hr⟩ := ih hSC
      let q : ℝ := (max a.re r + c) / 2
      have hmaxC : max a.re r < c := max_lt haC hrC
      refine ⟨q, by dsimp only [q]; linarith, ?_⟩
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hza | hz
      · rw [hza]
        have hle : a.re ≤ max a.re r := le_max_left _ _
        dsimp only [q]
        linarith
      · have hzr : z.re < r := hr z hz
        have hle : r ≤ max a.re r := le_max_right _ _
        dsimp only [q]
        linarith

/-- Local finiteness supplies a vertical cutoff strictly left of the critical line that avoids
both actual zeta and zeta-derivative divisors on a compact cutoff. -/
theorem exists_levinsonMontgomery_commonRightCutoff
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {l : ℝ} (hlHalf : l < 1 / 2) :
    ∃ r : ℝ, l < r ∧ r < 1 / 2 ∧
      (∀ u ∈ compactAnalyticDivisorSupportFinset riemannZeta K hK,
        u.re < 1 / 2 → u.re < r) ∧
      (∀ u ∈ compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK,
        u.re < 1 / 2 → u.re < r) ∧
      ∀ y : ℝ, (r : ℂ) + y * I ∈ K →
        riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 := by
  classical
  let Sz := compactAnalyticDivisorSupportFinset riemannZeta K hK
  let Sd := compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK
  let S : Finset ℂ :=
    insert (l : ℂ) ((Sz ∪ Sd).filter (fun z => z.re < 1 / 2))
  have hS : ∀ z ∈ S, z.re < 1 / 2 := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hz
    rcases hz with hzl | ⟨_, hzHalf⟩
    · subst z
      simpa using hlHalf
    · exact hzHalf
  obtain ⟨r, hrHalf, hr⟩ := exists_finset_re_strictUpperBound hS
  have hlr : l < r := by
    have hlS : (l : ℂ) ∈ S := by simp [S]
    simpa using hr (l : ℂ) hlS
  have hfZeta : AnalyticOnNhd ℂ riemannZeta K :=
    analyticOn_riemannZeta.mono hKDomain
  have hfDeriv : AnalyticOnNhd ℂ (deriv riemannZeta) K :=
    analyticOnNhd_deriv_riemannZeta.mono hKDomain
  have horderZeta : ∀ u : K, meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    intro u
    rw [(hfZeta u u.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_riemannZeta_ne_top_of_ne_one (hKDomain u.property)
  have horderDeriv : ∀ u : K,
      meromorphicOrderAt (deriv riemannZeta) u ≠ ⊤ := by
    intro u
    rw [(hfDeriv u u.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_deriv_riemannZeta_ne_top (hKDomain u.property)
  have hSzBound : ∀ u ∈ compactAnalyticDivisorSupportFinset riemannZeta K hK,
      u.re < 1 / 2 → u.re < r := by
    intro u hu huHalf
    apply hr u
    simp only [S, Finset.mem_insert, Finset.mem_filter, Finset.mem_union]
    exact Or.inr ⟨Or.inl hu, huHalf⟩
  have hSdBound : ∀ u ∈
      compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK,
      u.re < 1 / 2 → u.re < r := by
    intro u hu huHalf
    apply hr u
    simp only [S, Finset.mem_insert, Finset.mem_filter, Finset.mem_union]
    exact Or.inr ⟨Or.inr hu, huHalf⟩
  refine ⟨r, hlr, hrHalf, hSzBound, hSdBound, ?_⟩
  intro y hyK
  let z : ℂ := (r : ℂ) + y * I
  have hzK : z ∈ K := by simpa only [z] using hyK
  have hzRe : z.re = r := by simp [z]
  constructor
  · intro hzero
    have hzSupport :=
      mem_analytic_divisor_support_of_eq_zero hfZeta horderZeta hzK hzero
    have hzSz : z ∈ Sz := by
      exact mem_compactAnalyticDivisorSupportFinset.mpr hzSupport
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_insert, Finset.mem_filter, Finset.mem_union]
      exact Or.inr ⟨Or.inl hzSz, by rw [hzRe]; exact hrHalf⟩
    have hzlt := hr z hzS
    rw [hzRe] at hzlt
    exact (lt_irrefl r) hzlt
  · intro hzero
    have hzSupport :=
      mem_analytic_divisor_support_of_eq_zero hfDeriv horderDeriv hzK hzero
    have hzSd : z ∈ Sd := by
      exact mem_compactAnalyticDivisorSupportFinset.mpr hzSupport
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_insert, Finset.mem_filter, Finset.mem_union]
      exact Or.inr ⟨Or.inr hzSd, by rw [hzRe]; exact hrHalf⟩
    have hzlt := hr z hzS
    rw [hzRe] at hzlt
    exact (lt_irrefl r) hzlt

/-- An adaptive right cutoff converts common zero-free horizontal and left boundaries into an
actual zero-free rectangle count-difference identity while retaining every compact-cutoff divisor
point strictly left of the critical line. -/
theorem exists_levinsonMontgomery_zeroFreeRectangle_countDifference
    {K V : Set ℂ} {l b t : ℝ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hwideRect : ([[l, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ V)
    (hlHalf : l < 1 / 2) (hbt : b < t)
    (hbottom : ∀ x, l ≤ x → x < 1 / 2 →
      riemannZeta ((x : ℂ) + b * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + b * I) ≠ 0)
    (htop : ∀ x, l ≤ x → x < 1 / 2 →
      riemannZeta ((x : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + t * I) ≠ 0)
    (hleft : ∀ y ∈ [[b, t]],
      riemannZeta ((l : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((l : ℂ) + y * I) ≠ 0) :
    ∃ r : ℝ, l < r ∧ r < 1 / 2 ∧
      (∀ u ∈ compactAnalyticDivisorSupportFinset riemannZeta K hK,
        u.re < 1 / 2 → u.re < r) ∧
      (∀ u ∈ compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK,
        u.re < 1 / 2 → u.re < r) ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) l r b t -
          rectangleBoundaryIntegral (logDeriv riemannZeta) l r b t =
        2 * (Real.pi : ℂ) * I *
          ((∑ u ∈
              (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
                (pointStrictlyInsideRectangle l r b t),
              (MeromorphicOn.divisor (deriv riemannZeta) K u : ℂ)) -
            ∑ u ∈
              (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
                (pointStrictlyInsideRectangle l r b t),
              (MeromorphicOn.divisor riemannZeta K u : ℂ)) := by
  obtain ⟨r, hlr, hrHalf, hzetaBound, hderivBound, hright⟩ :=
    exists_levinsonMontgomery_commonRightCutoff hK hKDomain hlHalf
  have hhorSubset : [[l, r]] ⊆ [[l, (1 / 2 : ℝ)]] := by
    intro x hx
    rw [uIcc_of_le hlr.le] at hx
    rw [uIcc_of_le hlHalf.le]
    exact ⟨hx.1, hx.2.trans hrHalf.le⟩
  have hrWide : r ∈ [[l, (1 / 2 : ℝ)]] := by
    rw [uIcc_of_le hlHalf.le]
    exact ⟨hlr.le, hrHalf.le⟩
  have hrect : ([[l, r]] ×ℂ [[b, t]]) ⊆ V := by
    intro z hz
    exact hwideRect ⟨hhorSubset hz.1, hz.2⟩
  have hrightBoundary : ∀ y ∈ [[b, t]],
      riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 := by
    intro y hy
    apply hright y
    apply hVK
    apply hwideRect
    constructor
    · simpa using hrWide
    · simpa using hy
  have hbottomNarrow : ∀ x ∈ [[l, r]],
      riemannZeta ((x : ℂ) + b * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + b * I) ≠ 0 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc l r := by
      simpa only [uIcc_of_le hlr.le] using hx
    exact hbottom x hxIcc.1 (hxIcc.2.trans_lt hrHalf)
  have htopNarrow : ∀ x ∈ [[l, r]],
      riemannZeta ((x : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + t * I) ≠ 0 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc l r := by
      simpa only [uIcc_of_le hlr.le] using hx
    exact htop x hxIcc.1 (hxIcc.2.trans_lt hrHalf)
  have hdiff := levinsonMontgomery_zeroFreeRectangle_countDifference
    hK hKDomain hVOpen hVPre hVK hz0 hrect hlr hbt
      (fun x hx => (hbottomNarrow x hx).1)
      (fun x hx => (htopNarrow x hx).1)
      (fun y hy => (hrightBoundary y hy).1)
      (fun y hy => (hleft y hy).1)
      (fun x hx => (hbottomNarrow x hx).2)
      (fun x hx => (htopNarrow x hx).2)
      (fun y hy => (hrightBoundary y hy).2)
      (fun y hy => (hleft y hy).2)
  exact ⟨r, hlr, hrHalf, hzetaBound, hderivBound, hdiff⟩

/-- The adaptive finite-divisor count-difference certificate on the open upper-left strip between
two heights. -/
def LevinsonMontgomeryAdaptiveCountDifferenceAt
    (K : Set ℂ) (hK : IsCompact K) (b t : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
    (∀ u ∈ compactAnalyticDivisorSupportFinset riemannZeta K hK,
      u.re < 1 / 2 → u.re < r) ∧
    (∀ u ∈ compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK,
      u.re < 1 / 2 → u.re < r) ∧
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
      2 * (Real.pi : ℂ) * I *
        ((∑ u ∈
            (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
              (pointStrictlyInsideRectangle 0 r b t),
            (MeromorphicOn.divisor (deriv riemannZeta) K u : ℂ)) -
          ∑ u ∈
            (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
              (pointStrictlyInsideRectangle 0 r b t),
            (MeromorphicOn.divisor riemannZeta K u : ℂ))

/-- The compiled negative-height geometry supplies an exact adaptive count-difference contour.
If zeta vanishes at the critical endpoint, the endpoint is excluded by finite-support
stabilization rather than silently placed on the path. -/
theorem levinsonMontgomery_adaptiveCountDifference_of_negativeHeightGeometry
    {K V : Set ℂ} {b : ℝ} {n : ℕ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hwideRect : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, (n : ℝ)]]) ⊆ V)
    (hbTen : 10 ≤ b) (hbn : b < n)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : LevinsonMontgomeryNegativeHeightGeometry n) :
    LevinsonMontgomeryAdaptiveCountDifferenceAt K hK b n := by
  apply exists_levinsonMontgomery_zeroFreeRectangle_countDifference
    hK hKDomain hVOpen hVPre hVK hz0 hwideRect (by norm_num) hbn
  · intro x hx0 hxHalf
    exact hbottom.2 x ⟨hx0, hxHalf.le⟩
  · intro x hx0 hxHalf
    have hx := htop.1 x hx0 hxHalf
    have hnCast : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_num
    rw [hnCast]
    simpa only [levinsonMontgomeryIntegerPoint] using And.intro hx.1 hx.2.1
  · intro y hy
    have hyIcc : y ∈ Set.Icc b (n : ℝ) := by
      simpa only [uIcc_of_le hbn.le] using hy
    let s : ℂ := (0 : ℂ) + y * I
    have hsRe : s.re = 0 := by simp [s]
    have hsIm : 10 ≤ s.im := by
      have hsImEq : s.im = y := by simp [s]
      rw [hsImEq]
      exact hbTen.trans hyIcc.1
    have hsData :=
      levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_left_boundary hsRe hsIm
    have hsDeriv : deriv riemannZeta s ≠ 0 := by
      intro hzero
      have hneg := hsData.2
      rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hneg
      exact (lt_irrefl 0) hneg
    simpa [s] using And.intro hsData.1 hsDeriv

/-- Multiplicity-bearing zeta count in a strict rectangle, using a compact divisor cutoff. -/
def compactZetaStrictRectangleCount
    (K : Set ℂ) (hK : IsCompact K) (l r b t : ℝ) : ℕ :=
  ∑ u ∈ (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
      (pointStrictlyInsideRectangle l r b t), burnolZetaZeroMultiplicity u

/-- Multiplicity-bearing zeta-derivative count in a strict rectangle, using a compact divisor
cutoff. -/
def compactZetaDerivStrictRectangleCount
    (K : Set ℂ) (hK : IsCompact K) (l r b t : ℝ) : ℕ :=
  ∑ u ∈ (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
      (pointStrictlyInsideRectangle l r b t), riemannZetaDerivZeroMultiplicity u

/-- On a pole-free cutoff, the zeta divisor value is its canonical natural analytic
multiplicity. -/
theorem divisor_riemannZeta_eq_burnolMultiplicity
    {K : Set ℂ} (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ) {u : ℂ} (huK : u ∈ K) :
    MeromorphicOn.divisor riemannZeta K u = (burnolZetaZeroMultiplicity u : ℤ) := by
  have hf : AnalyticOnNhd ℂ riemannZeta K :=
    analyticOn_riemannZeta.mono hKDomain
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf huK,
    ← Nat.cast_analyticOrderNatAt
      (analyticOrderAt_riemannZeta_ne_top_of_ne_one (hKDomain huK))]
  simp [burnolZetaZeroMultiplicity]

/-- On a pole-free cutoff, the zeta-derivative divisor value is its canonical natural analytic
multiplicity. -/
theorem divisor_deriv_riemannZeta_eq_multiplicity
    {K : Set ℂ} (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ) {u : ℂ} (huK : u ∈ K) :
    MeromorphicOn.divisor (deriv riemannZeta) K u =
      (riemannZetaDerivZeroMultiplicity u : ℤ) := by
  have hf : AnalyticOnNhd ℂ (deriv riemannZeta) K :=
    analyticOnNhd_deriv_riemannZeta.mono hKDomain
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf huK,
    ← Nat.cast_analyticOrderNatAt
      (analyticOrderAt_deriv_riemannZeta_ne_top (hKDomain huK))]
  simp [riemannZetaDerivZeroMultiplicity]

/-- The complex zeta-divisor sum in a strict rectangle is the cast of the compact natural count. -/
theorem sum_divisor_riemannZeta_eq_compactCount
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (l r b t : ℝ) :
    (∑ u ∈ (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
        (pointStrictlyInsideRectangle l r b t),
        (MeromorphicOn.divisor riemannZeta K u : ℂ)) =
      (compactZetaStrictRectangleCount K hK l r b t : ℂ) := by
  unfold compactZetaStrictRectangleCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have huSupport : u ∈ (MeromorphicOn.divisor riemannZeta K).support := by
    apply mem_compactAnalyticDivisorSupportFinset.mp
    exact (Finset.mem_filter.mp hu).1
  rw [divisor_riemannZeta_eq_burnolMultiplicity hKDomain
    ((MeromorphicOn.divisor riemannZeta K).supportWithinDomain huSupport)]
  norm_num

/-- The complex zeta-derivative divisor sum in a strict rectangle is the cast of the compact
natural count. -/
theorem sum_divisor_deriv_riemannZeta_eq_compactCount
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (l r b t : ℝ) :
    (∑ u ∈ (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
        (pointStrictlyInsideRectangle l r b t),
        (MeromorphicOn.divisor (deriv riemannZeta) K u : ℂ)) =
      (compactZetaDerivStrictRectangleCount K hK l r b t : ℂ) := by
  unfold compactZetaDerivStrictRectangleCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have huSupport : u ∈ (MeromorphicOn.divisor (deriv riemannZeta) K).support := by
    apply mem_compactAnalyticDivisorSupportFinset.mp
    exact (Finset.mem_filter.mp hu).1
  rw [divisor_deriv_riemannZeta_eq_multiplicity hKDomain
    ((MeromorphicOn.divisor (deriv riemannZeta) K).supportWithinDomain huSupport)]
  norm_num

/-- A right cutoff lying left of `1/2` and to the right of every relevant finite support point
selects exactly the same strict-rectangle finset as the open critical-line boundary. -/
theorem filter_pointStrictlyInsideRectangle_eq_criticalLine
    {S : Finset ℂ} {r b t : ℝ} (hrHalf : r < 1 / 2)
    (hbound : ∀ u ∈ S, u.re < 1 / 2 → u.re < r) :
    S.filter (pointStrictlyInsideRectangle 0 r b t) =
      S.filter (pointStrictlyInsideRectangle 0 (1 / 2) b t) := by
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, h0, hur, hb, ht⟩
    exact ⟨hu, h0, hur.trans hrHalf, hb, ht⟩
  · rintro ⟨hu, h0, huHalf, hb, ht⟩
    exact ⟨hu, h0, hbound u hu huHalf, hb, ht⟩

theorem compactZetaStrictRectangleCount_eq_criticalLine_of_rightCutoff
    {K : Set ℂ} (hK : IsCompact K) {r b t : ℝ} (hrHalf : r < 1 / 2)
    (hbound : ∀ u ∈ compactAnalyticDivisorSupportFinset riemannZeta K hK,
      u.re < 1 / 2 → u.re < r) :
    compactZetaStrictRectangleCount K hK 0 r b t =
      compactZetaStrictRectangleCount K hK 0 (1 / 2) b t := by
  unfold compactZetaStrictRectangleCount
  rw [filter_pointStrictlyInsideRectangle_eq_criticalLine hrHalf hbound]

theorem compactZetaDerivStrictRectangleCount_eq_criticalLine_of_rightCutoff
    {K : Set ℂ} (hK : IsCompact K) {r b t : ℝ} (hrHalf : r < 1 / 2)
    (hbound : ∀ u ∈ compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK,
      u.re < 1 / 2 → u.re < r) :
    compactZetaDerivStrictRectangleCount K hK 0 r b t =
      compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b t := by
  unfold compactZetaDerivStrictRectangleCount
  rw [filter_pointStrictlyInsideRectangle_eq_criticalLine hrHalf hbound]

/-- The adaptive divisor certificate is exactly a difference of natural multiplicity counts on
the source open-left convention. -/
theorem levinsonMontgomery_adaptiveCountDifference_eq_compactCounts
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {b t : ℝ} (hcert : LevinsonMontgomeryAdaptiveCountDifferenceAt K hK b t) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
        2 * (Real.pi : ℂ) * I *
          ((compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b t : ℂ) -
            (compactZetaStrictRectangleCount K hK 0 (1 / 2) b t : ℂ)) := by
  rcases hcert with ⟨r, hr0, hrHalf, hzetaBound, hderivBound, hdiff⟩
  have hzetaCount :=
    compactZetaStrictRectangleCount_eq_criticalLine_of_rightCutoff
      hK (b := b) (t := t) hrHalf hzetaBound
  have hderivCount :=
    compactZetaDerivStrictRectangleCount_eq_criticalLine_of_rightCutoff
      hK (b := b) (t := t) hrHalf hderivBound
  rw [sum_divisor_deriv_riemannZeta_eq_compactCount hK hKDomain 0 r b t,
    sum_divisor_riemannZeta_eq_compactCount hK hKDomain 0 r b t,
    hzetaCount, hderivCount] at hdiff
  exact ⟨r, hr0, hrHalf, hdiff⟩

/-- Negative-height source geometry yields the exact contour identity for the natural
multiplicity counts in the open upper-left rectangle between the fixed bottom and that height. -/
theorem levinsonMontgomery_compactCountDifference_of_negativeHeightGeometry
    {K V : Set ℂ} {b : ℝ} {n : ℕ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hwideRect : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, (n : ℝ)]]) ⊆ V)
    (hbTen : 10 ≤ b) (hbn : b < n)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : LevinsonMontgomeryNegativeHeightGeometry n) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b n -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b n =
        2 * (Real.pi : ℂ) * I *
          ((compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b n : ℂ) -
            (compactZetaStrictRectangleCount K hK 0 (1 / 2) b n : ℂ)) := by
  apply levinsonMontgomery_adaptiveCountDifference_eq_compactCounts hK hKDomain
  exact levinsonMontgomery_adaptiveCountDifference_of_negativeHeightGeometry
    hK hKDomain hVOpen hVPre hVK hz0 hwideRect hbTen hbn hbottom htop

/-- The compact zeta support in the strict source rectangle is exactly the global source zero
finset below `t`, filtered to heights above `b`. -/
theorem compactZeta_strictRectangleFinset_eq_speiser_filter
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {b t : ℝ} (hb0 : 0 ≤ b) (hbt : b < t)
    (hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ K) :
    (compactAnalyticDivisorSupportFinset riemannZeta K hK).filter
        (pointStrictlyInsideRectangle 0 (1 / 2) b t) =
      (speiserUpperLeftZetaZeroFinset t).filter (fun u => b < u.im) := by
  classical
  have hf : AnalyticOnNhd ℂ riemannZeta K :=
    analyticOn_riemannZeta.mono hKDomain
  have horder : ∀ u : K, meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    intro u
    rw [(hf u u.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_riemannZeta_ne_top_of_ne_one (hKDomain u.property)
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, hinside⟩
    have huSupport : u ∈ (MeromorphicOn.divisor riemannZeta K).support :=
      mem_compactAnalyticDivisorSupportFinset.mp hu
    have hzero := eq_zero_of_mem_analytic_divisor_support hf huSupport
    have hstrip : u ∈ speiserUpperLeftStrip :=
      ⟨hb0.trans_lt hinside.2.2.1, hinside.1, hinside.2.1⟩
    have hnontrivial := isNontrivialZero_of_mem_speiserUpperLeftStrip hstrip hzero
    refine ⟨mem_speiserUpperLeftZetaZeroFinset.mpr ⟨⟨hstrip, hinside.2.2.2⟩,
      hnontrivial⟩, hinside.2.2.1⟩
  · rintro ⟨hu, hbIm⟩
    have huData := mem_speiserUpperLeftZetaZeroFinset.mp hu
    have huK : u ∈ K := by
      apply hrectK
      constructor
      · rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact ⟨huData.1.1.2.1.le, huData.1.1.2.2.le⟩
      · rw [uIcc_of_le hbt.le]
        exact ⟨hbIm.le, huData.1.2.le⟩
    refine ⟨mem_compactAnalyticDivisorSupportFinset.mpr
      (mem_analytic_divisor_support_of_eq_zero hf horder huK huData.2.1), ?_⟩
    exact ⟨huData.1.1.2.1, huData.1.1.2.2, hbIm, huData.1.2⟩

/-- The analogous compact-support identification for actual zeta-derivative zeros. -/
theorem compactZetaDeriv_strictRectangleFinset_eq_speiser_filter
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {b t : ℝ} (hb0 : 0 ≤ b) (hbt : b < t)
    (hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ K) :
    (compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK).filter
        (pointStrictlyInsideRectangle 0 (1 / 2) b t) =
      (speiserUpperLeftDerivZeroFinset t).filter (fun u => b < u.im) := by
  classical
  have hf : AnalyticOnNhd ℂ (deriv riemannZeta) K :=
    analyticOnNhd_deriv_riemannZeta.mono hKDomain
  have horder : ∀ u : K,
      meromorphicOrderAt (deriv riemannZeta) u ≠ ⊤ := by
    intro u
    rw [(hf u u.property).meromorphicOrderAt_eq]
    simpa using analyticOrderAt_deriv_riemannZeta_ne_top (hKDomain u.property)
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, hinside⟩
    have huSupport : u ∈
        (MeromorphicOn.divisor (deriv riemannZeta) K).support :=
      mem_compactAnalyticDivisorSupportFinset.mp hu
    have hzero := eq_zero_of_mem_analytic_divisor_support hf huSupport
    have hstrip : u ∈ speiserUpperLeftStrip :=
      ⟨hb0.trans_lt hinside.2.2.1, hinside.1, hinside.2.1⟩
    exact ⟨mem_speiserUpperLeftDerivZeroFinset.mpr
      ⟨⟨hstrip, hinside.2.2.2⟩, hzero⟩, hinside.2.2.1⟩
  · rintro ⟨hu, hbIm⟩
    have huData := mem_speiserUpperLeftDerivZeroFinset.mp hu
    have huK : u ∈ K := by
      apply hrectK
      constructor
      · rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact ⟨huData.1.1.2.1.le, huData.1.1.2.2.le⟩
      · rw [uIcc_of_le hbt.le]
        exact ⟨hbIm.le, huData.1.2.le⟩
    refine ⟨mem_compactAnalyticDivisorSupportFinset.mpr
      (mem_analytic_divisor_support_of_eq_zero hf horder huK huData.2), ?_⟩
    exact ⟨huData.1.1.2.1, huData.1.1.2.2, hbIm, huData.1.2⟩

theorem speiserUpperLeftZetaZeroFinset_filter_im_lt
    {b t : ℝ} (hbt : b < t) :
    (speiserUpperLeftZetaZeroFinset t).filter (fun u => u.im < b) =
      speiserUpperLeftZetaZeroFinset b := by
  ext u
  simp only [Finset.mem_filter, mem_speiserUpperLeftZetaZeroFinset]
  constructor
  · rintro ⟨⟨⟨hstrip, _⟩, hzero⟩, huIm⟩
    exact ⟨⟨hstrip, huIm⟩, hzero⟩
  · rintro ⟨⟨hstrip, huIm⟩, hzero⟩
    exact ⟨⟨⟨hstrip, huIm.trans hbt⟩, hzero⟩, huIm⟩

theorem speiserUpperLeftDerivZeroFinset_filter_im_lt
    {b t : ℝ} (hbt : b < t) :
    (speiserUpperLeftDerivZeroFinset t).filter (fun u => u.im < b) =
      speiserUpperLeftDerivZeroFinset b := by
  ext u
  simp only [Finset.mem_filter, mem_speiserUpperLeftDerivZeroFinset]
  constructor
  · rintro ⟨⟨⟨hstrip, _⟩, hzero⟩, huIm⟩
    exact ⟨⟨hstrip, huIm⟩, hzero⟩
  · rintro ⟨⟨hstrip, huIm⟩, hzero⟩
    exact ⟨⟨⟨hstrip, huIm.trans hbt⟩, hzero⟩, huIm⟩

theorem speiserUpperLeftZetaZeroFinset_filter_not_im_lt
    {b t : ℝ} (hbottom : SpeiserCommonZeroFreeHorizontal b) :
    (speiserUpperLeftZetaZeroFinset t).filter (fun u => ¬u.im < b) =
      (speiserUpperLeftZetaZeroFinset t).filter (fun u => b < u.im) := by
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, hnotlt⟩
    have huData := mem_speiserUpperLeftZetaZeroFinset.mp hu
    refine ⟨hu, lt_of_le_of_ne (le_of_not_gt hnotlt) ?_⟩
    intro hEq
    have hreIcc : u.re ∈ Set.Icc (0 : ℝ) (1 / 2) :=
      ⟨huData.1.1.2.1.le, huData.1.1.2.2.le⟩
    have hpoint : (u.re : ℂ) + b * I = u := by
      apply Complex.ext
      · simp
      · simp [hEq]
    apply (hbottom.2 u.re hreIcc).1
    rw [hpoint]
    exact huData.2.1
  · rintro ⟨hu, hlt⟩
    exact ⟨hu, not_lt.mpr hlt.le⟩

theorem speiserUpperLeftDerivZeroFinset_filter_not_im_lt
    {b t : ℝ} (hbottom : SpeiserCommonZeroFreeHorizontal b) :
    (speiserUpperLeftDerivZeroFinset t).filter (fun u => ¬u.im < b) =
      (speiserUpperLeftDerivZeroFinset t).filter (fun u => b < u.im) := by
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, hnotlt⟩
    have huData := mem_speiserUpperLeftDerivZeroFinset.mp hu
    refine ⟨hu, lt_of_le_of_ne (le_of_not_gt hnotlt) ?_⟩
    intro hEq
    have hreIcc : u.re ∈ Set.Icc (0 : ℝ) (1 / 2) :=
      ⟨huData.1.1.2.1.le, huData.1.1.2.2.le⟩
    have hpoint : (u.re : ℂ) + b * I = u := by
      apply Complex.ext
      · simp
      · simp [hEq]
    apply (hbottom.2 u.re hreIcc).2
    rw [hpoint]
    exact huData.2
  · rintro ⟨hu, hlt⟩
    exact ⟨hu, not_lt.mpr hlt.le⟩

/-- The global zeta count below `t` splits into the count below a common zero-free bottom and the
compact strict-rectangle count between the two heights. -/
theorem speiserUpperLeftZetaZeroCount_add_compactCount
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {b t : ℝ} (hbt : b < t) (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ K) :
    speiserUpperLeftZetaZeroCount b +
        compactZetaStrictRectangleCount K hK 0 (1 / 2) b t =
      speiserUpperLeftZetaZeroCount t := by
  unfold speiserUpperLeftZetaZeroCount compactZetaStrictRectangleCount
  rw [compactZeta_strictRectangleFinset_eq_speiser_filter
    hK hKDomain hbottom.1.le hbt hrectK]
  rw [← speiserUpperLeftZetaZeroFinset_filter_im_lt hbt,
    ← speiserUpperLeftZetaZeroFinset_filter_not_im_lt hbottom]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- The corresponding height split for the actual zeta-derivative count. -/
theorem speiserUpperLeftDerivZeroCount_add_compactCount
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {b t : ℝ} (hbt : b < t) (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ K) :
    speiserUpperLeftDerivZeroCount b +
        compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b t =
      speiserUpperLeftDerivZeroCount t := by
  unfold speiserUpperLeftDerivZeroCount compactZetaDerivStrictRectangleCount
  rw [compactZetaDeriv_strictRectangleFinset_eq_speiser_filter
    hK hKDomain hbottom.1.le hbt hrectK]
  rw [← speiserUpperLeftDerivZeroFinset_filter_im_lt hbt,
    ← speiserUpperLeftDerivZeroFinset_filter_not_im_lt hbottom]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Exact Levinson--Montgomery count-difference identity at a negative-height geometry witness,
stated with the project's global multiplicity-bearing source counts. -/
theorem levinsonMontgomery_globalCountDifference_of_negativeHeightGeometry
    {K V : Set ℂ} {b : ℝ} {n : ℕ}
    (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    (hVOpen : IsOpen V) (hVPre : IsPreconnected V) (hVK : V ⊆ K)
    {z0 : ℂ} (hz0 : z0 ∈ V)
    (hwideRect : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, (n : ℝ)]]) ⊆ V)
    (hbTen : 10 ≤ b) (hbn : b < n)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : LevinsonMontgomeryNegativeHeightGeometry n) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b n -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b n =
        2 * (Real.pi : ℂ) * I *
          (((speiserUpperLeftDerivZeroCount n : ℂ) -
              (speiserUpperLeftZetaZeroCount n : ℂ)) -
            ((speiserUpperLeftDerivZeroCount b : ℂ) -
              (speiserUpperLeftZetaZeroCount b : ℂ))) := by
  have hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, (n : ℝ)]]) ⊆ K :=
    fun _ hz => hVK (hwideRect hz)
  obtain ⟨r, hr0, hrHalf, hdiff⟩ :=
    levinsonMontgomery_compactCountDifference_of_negativeHeightGeometry
      hK hKDomain hVOpen hVPre hVK hz0 hwideRect hbTen hbn hbottom htop
  have hzetaSplit := speiserUpperLeftZetaZeroCount_add_compactCount
    hK hKDomain hbn hbottom hrectK
  have hderivSplit := speiserUpperLeftDerivZeroCount_add_compactCount
    hK hKDomain hbn hbottom hrectK
  have hzetaCast :
      (speiserUpperLeftZetaZeroCount b : ℂ) +
          (compactZetaStrictRectangleCount K hK 0 (1 / 2) b n : ℂ) =
        (speiserUpperLeftZetaZeroCount n : ℂ) := by
    exact_mod_cast hzetaSplit
  have hderivCast :
      (speiserUpperLeftDerivZeroCount b : ℂ) +
          (compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b n : ℂ) =
        (speiserUpperLeftDerivZeroCount n : ℂ) := by
    exact_mod_cast hderivSplit
  have hzetaCompact :
      (compactZetaStrictRectangleCount K hK 0 (1 / 2) b n : ℂ) =
        (speiserUpperLeftZetaZeroCount n : ℂ) -
          (speiserUpperLeftZetaZeroCount b : ℂ) := by
    linear_combination hzetaCast
  have hderivCompact :
      (compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b n : ℂ) =
        (speiserUpperLeftDerivZeroCount n : ℂ) -
          (speiserUpperLeftDerivZeroCount b : ℂ) := by
    linear_combination hderivCast
  rw [hzetaCompact, hderivCompact] at hdiff
  refine ⟨r, hr0, hrHalf, ?_⟩
  calc
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b n -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b n =
      2 * (Real.pi : ℂ) * I *
        (((speiserUpperLeftDerivZeroCount n : ℂ) -
            (speiserUpperLeftDerivZeroCount b : ℂ)) -
          ((speiserUpperLeftZetaZeroCount n : ℂ) -
            (speiserUpperLeftZetaZeroCount b : ℂ))) := hdiff
    _ = 2 * (Real.pi : ℂ) * I *
        (((speiserUpperLeftDerivZeroCount n : ℂ) -
            (speiserUpperLeftZetaZeroCount n : ℂ)) -
          ((speiserUpperLeftDerivZeroCount b : ℂ) -
            (speiserUpperLeftZetaZeroCount b : ℂ))) := by ring

/-- A concrete compact cutoff leaving unit vertical margin and staying strictly left of the zeta
pole. -/
def levinsonMontgomeryCountCompactCutoff (b t : ℝ) : Set ℂ :=
  Set.Icc (-1 : ℝ) (3 / 4) ×ℂ Set.Icc (b - 1) (t + 1)

/-- The connected open interior used for the finite-factorization identity theorem. -/
def levinsonMontgomeryCountOpenCutoff (b t : ℝ) : Set ℂ :=
  Set.Ioo (-1 : ℝ) (3 / 4) ×ℂ Set.Ioo (b - 1) (t + 1)

theorem isCompact_levinsonMontgomeryCountCompactCutoff (b t : ℝ) :
    IsCompact (levinsonMontgomeryCountCompactCutoff b t) := by
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem levinsonMontgomeryCountCompactCutoff_subset_zetaDomain (b t : ℝ) :
    levinsonMontgomeryCountCompactCutoff b t ⊆ ({1} : Set ℂ)ᶜ := by
  intro z hz hzOne
  subst z
  have hre := hz.1.2
  norm_num [levinsonMontgomeryCountCompactCutoff] at hre

theorem isOpen_levinsonMontgomeryCountOpenCutoff (b t : ℝ) :
    IsOpen (levinsonMontgomeryCountOpenCutoff b t) := by
  exact isOpen_Ioo.reProdIm isOpen_Ioo

theorem isPreconnected_levinsonMontgomeryCountOpenCutoff (b t : ℝ) :
    IsPreconnected (levinsonMontgomeryCountOpenCutoff b t) := by
  have hconvex : Convex ℝ
      ({z : ℂ | (-1 : ℝ) < z.re} ∩ {z : ℂ | z.re < 3 / 4} ∩
        {z : ℂ | b - 1 < z.im} ∩ {z : ℂ | z.im < t + 1}) :=
    (((convex_halfSpace_re_gt (-1 : ℝ)).inter
      (convex_halfSpace_re_lt (3 / 4))).inter
        (convex_halfSpace_im_gt (b - 1))).inter
          (convex_halfSpace_im_lt (t + 1))
  have hset :
      levinsonMontgomeryCountOpenCutoff b t =
        ({z : ℂ | (-1 : ℝ) < z.re} ∩ {z : ℂ | z.re < 3 / 4} ∩
          {z : ℂ | b - 1 < z.im} ∩ {z : ℂ | z.im < t + 1}) := by
    ext z
    simp [levinsonMontgomeryCountOpenCutoff, mem_reProdIm, and_assoc]
  rw [hset]
  exact hconvex.isPreconnected

theorem levinsonMontgomeryCountOpenCutoff_subset_compact (b t : ℝ) :
    levinsonMontgomeryCountOpenCutoff b t ⊆
      levinsonMontgomeryCountCompactCutoff b t := by
  intro z hz
  simp only [levinsonMontgomeryCountOpenCutoff,
    levinsonMontgomeryCountCompactCutoff, mem_reProdIm] at hz ⊢
  constructor
  · exact ⟨hz.1.1.le, hz.1.2.le⟩
  · exact ⟨hz.2.1.le, hz.2.2.le⟩

theorem levinsonMontgomery_sourceRectangle_subset_openCutoff
    {b t : ℝ} (hbt : b < t) :
    ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆
      levinsonMontgomeryCountOpenCutoff b t := by
  intro z hz
  rw [mem_reProdIm] at hz
  simp only [levinsonMontgomeryCountOpenCutoff, mem_reProdIm]
  have hre : z.re ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hz.1
  have him : z.im ∈ Set.Icc b t := by
    simpa only [uIcc_of_le hbt.le] using hz.2
  constructor
  · constructor <;> linarith [hre.1, hre.2]
  · constructor <;> linarith [him.1, him.2]

theorem exists_mem_levinsonMontgomeryCountOpenCutoff
    {b t : ℝ} (hbt : b < t) :
    (1 / 4 : ℂ) + b * I ∈ levinsonMontgomeryCountOpenCutoff b t := by
  constructor
  · norm_num
  · constructor
    · norm_num
    · norm_num
      linarith

/-- Fully instantiated exact count-difference identity. All compact/open cutoff objects and their
topological side conditions are discharged internally. -/
theorem levinsonMontgomery_globalCountDifference_actual
    {b : ℝ} {n : ℕ} (hbTen : 10 ≤ b) (hbn : b < n)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : LevinsonMontgomeryNegativeHeightGeometry n) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b n -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b n =
        2 * (Real.pi : ℂ) * I *
          (((speiserUpperLeftDerivZeroCount n : ℂ) -
              (speiserUpperLeftZetaZeroCount n : ℂ)) -
            ((speiserUpperLeftDerivZeroCount b : ℂ) -
              (speiserUpperLeftZetaZeroCount b : ℂ))) := by
  exact levinsonMontgomery_globalCountDifference_of_negativeHeightGeometry
    (K := levinsonMontgomeryCountCompactCutoff b n)
    (V := levinsonMontgomeryCountOpenCutoff b n)
    (isCompact_levinsonMontgomeryCountCompactCutoff b n)
    (levinsonMontgomeryCountCompactCutoff_subset_zetaDomain b n)
    (isOpen_levinsonMontgomeryCountOpenCutoff b n)
    (isPreconnected_levinsonMontgomeryCountOpenCutoff b n)
    (levinsonMontgomeryCountOpenCutoff_subset_compact b n)
    (exists_mem_levinsonMontgomeryCountOpenCutoff hbn)
    (levinsonMontgomery_sourceRectangle_subset_openCutoff hbn)
    hbTen hbn hbottom htop

end

end LeanLab.Riemann
