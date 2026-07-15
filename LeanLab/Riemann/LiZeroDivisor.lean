import LeanLab.Riemann.LiScaffold
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm

set_option linter.style.header false

/-!
# The global xi zero divisor

This file packages the zeros of the project-local `riemannXi` as a locally finite divisor with
their analytic multiplicities. The support is aligned exactly with `IsNontrivialZero`; in
particular, the negative even zeta zeros are proved not to be zeros of `riemannXi`.
-/

namespace LeanLab.Riemann

open Complex Filter Function Set
open scoped Topology

noncomputable section

theorem analyticOnNhd_riemannXi :
    AnalyticOnNhd ℂ riemannXi univ :=
  analyticOnNhd_univ_iff_differentiable.mpr differentiable_riemannXi

theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hcompleted : completedRiemannZeta s ≠ 0 := by
    intro hzero
    apply riemannZeta_ne_zero_of_one_lt_re hs
    rw [riemannZeta_def_of_ne_zero hs0, hzero]
    simp
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)) hcompleted

theorem riemannXi_ne_zero_of_isTrivialZeroPoint {s : ℂ}
    (hs : IsTrivialZeroPoint s) :
    riemannXi s ≠ 0 := by
  rcases hs with ⟨n, rfl⟩
  rw [← riemannXi_one_sub (-2 * (n + 1) : ℂ)]
  apply riemannXi_ne_zero_of_one_lt_re
  norm_num
  positivity

theorem isNontrivialZero_iff_riemannXi_eq_zero (s : ℂ) :
    IsNontrivialZero s ↔ riemannXi s = 0 := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial]
  constructor
  · exact And.left
  · intro hzero
    exact ⟨hzero, fun htrivial => riemannXi_ne_zero_of_isTrivialZeroPoint htrivial hzero⟩

theorem analyticOrderAt_riemannXi_ne_top (s : ℂ) :
    analyticOrderAt riemannXi s ≠ ⊤ := by
  intro htop
  have hlocal : riemannXi =ᶠ[𝓝 s] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hglobal : riemannXi = (0 : ℂ → ℂ) :=
    analyticOnNhd_riemannXi.eq_of_eventuallyEq analyticOnNhd_const hlocal
  have hone := congrFun hglobal 1
  rw [riemannXi_one] at hone
  norm_num at hone

theorem meromorphicOrderAt_riemannXi_ne_top (s : ℂ) :
    meromorphicOrderAt riemannXi s ≠ ⊤ := by
  intro htop
  rw [(analyticAt_riemannXi s).meromorphicOrderAt_eq] at htop
  exact analyticOrderAt_riemannXi_ne_top s (ENat.map_eq_top_iff.mp htop)

/-- The finite natural order of vanishing of `riemannXi` at `s`. -/
def riemannXiZeroMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt riemannXi s

theorem riemannXiZeroMultiplicity_pos_iff (s : ℂ) :
    0 < riemannXiZeroMultiplicity s ↔ IsNontrivialZero s := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero]
  constructor
  · intro hpos
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_of_gt hpos)
  · intro hzero
    apply Nat.pos_of_ne_zero
    intro horder
    have hfinite := analyticOrderAt_riemannXi_ne_top s
    have hne : analyticOrderAt riemannXi s ≠ 0 :=
      (analyticAt_riemannXi s).analyticOrderAt_ne_zero.mpr hzero
    apply hne
    change analyticOrderNatAt riemannXi s = 0 at horder
    rw [← Nat.cast_analyticOrderNatAt hfinite, horder]
    simp

/-- The globally locally finite divisor of the project-local xi function. -/
def riemannXiZeroDivisor : Function.locallyFinsupp ℂ ℤ :=
  MeromorphicOn.divisor riemannXi univ

theorem riemannXiZeroDivisor_apply (s : ℂ) :
    riemannXiZeroDivisor s = (riemannXiZeroMultiplicity s : ℤ) := by
  rw [riemannXiZeroDivisor,
    MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (mem_univ s),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top s)]
  simp [riemannXiZeroMultiplicity]

theorem support_riemannXiZeroDivisor :
    Function.support riemannXiZeroDivisor = {s : ℂ | IsNontrivialZero s} := by
  ext s
  rw [Function.mem_support, Set.mem_setOf_eq, riemannXiZeroDivisor_apply]
  constructor
  · intro hne
    exact (riemannXiZeroMultiplicity_pos_iff s).mp
      (Nat.pos_of_ne_zero (by exact_mod_cast hne))
  · intro hzero
    have hpos := (riemannXiZeroMultiplicity_pos_iff s).mpr hzero
    exact_mod_cast Nat.ne_of_gt hpos

theorem compact_inter_nontrivialZeros_finite {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {s : ℂ | IsNontrivialZero s}).Finite := by
  rw [← support_riemannXiZeroDivisor]
  exact riemannXiZeroDivisor.locallyFiniteSupport.finite_inter_support_of_isCompact hK

theorem analyticOrderAt_riemannXi_one_sub (s : ℂ) :
    analyticOrderAt riemannXi (1 - s) = analyticOrderAt riemannXi s := by
  let reflect : ℂ → ℂ := fun z => 1 - z
  have hreflectAnalytic : AnalyticAt ℂ reflect s := by
    fun_prop
  have hreflectDeriv : deriv reflect s ≠ 0 := by
    simp [reflect, deriv_const_sub_id]
  have hcomp :
      analyticOrderAt (riemannXi ∘ reflect) s =
        analyticOrderAt riemannXi (reflect s) :=
    analyticOrderAt_comp_of_deriv_ne_zero hreflectAnalytic hreflectDeriv
  have hfunctional :
      analyticOrderAt (riemannXi ∘ reflect) s = analyticOrderAt riemannXi s := by
    apply analyticOrderAt_congr
    exact Filter.Eventually.of_forall fun z => by
      simpa [reflect, Function.comp_def] using riemannXi_one_sub z
  calc
    analyticOrderAt riemannXi (1 - s) = analyticOrderAt (riemannXi ∘ reflect) s := by
      simpa [reflect] using hcomp.symm
    _ = analyticOrderAt riemannXi s := hfunctional

theorem riemannXiZeroMultiplicity_one_sub (s : ℂ) :
    riemannXiZeroMultiplicity (1 - s) = riemannXiZeroMultiplicity s := by
  simpa [riemannXiZeroMultiplicity, analyticOrderNatAt] using
    congrArg ENat.toNat (analyticOrderAt_riemannXi_one_sub s)

theorem riemannXiZeroDivisor_one_sub (s : ℂ) :
    riemannXiZeroDivisor (1 - s) = riemannXiZeroDivisor s := by
  rw [riemannXiZeroDivisor_apply, riemannXiZeroDivisor_apply,
    riemannXiZeroMultiplicity_one_sub]

end

end LeanLab.Riemann
