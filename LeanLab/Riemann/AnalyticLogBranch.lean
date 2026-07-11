import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LeanLab.Riemann.Basic

set_option linter.style.header false

/-!
# Holomorphic logarithm branches

This module upgrades the continuous logarithm branch supplied by mathlib on simply connected
domains to a holomorphic branch. This is the first analytic input in the zero-free-half-plane
argument used by Titchmarsh and Balazard-Saias to bound the reciprocal zeta function.
-/

noncomputable section

open Set

namespace Complex

/-- A nonvanishing holomorphic function on a simply connected open set has a holomorphic
logarithm branch. The derivative of every such branch is the logarithmic derivative of the
original function. -/
theorem exists_differentiableOn_eqOn_exp_comp_of_isSimplyConnected
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg₀ : 0 ∉ g '' U) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧ EqOn (exp ∘ f) g U ∧
        ∀ z ∈ U, HasDerivAt f (deriv g z / g z) z := by
  obtain ⟨f, hfc, hfexp⟩ :=
    exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn hg₀
  have hderiv : ∀ z ∈ U, HasDerivAt f (deriv g z / g z) z := by
    intro z hz
    have hgz : g z ≠ 0 := by
      intro hzero
      exact hg₀ ⟨z, hz, hzero⟩
    have hgd : DifferentiableAt ℂ g z :=
      (hg z hz).differentiableAt (hUo.mem_nhds hz)
    have hlog :
        HasDerivAt (fun w : ℂ => log (g w / g z)) (deriv g z / g z) z := by
      convert hgd.hasDerivAt.div_const (g z) |>.clog (by simp [hgz]) using 1
      all_goals simp [hgz]
    have hfc_at : ContinuousAt f z := hfc.continuousAt (hUo.mem_nhds hz)
    have hf_sub_tendsto :
        Filter.Tendsto (fun w : ℂ => f w - f z) (nhds z) (nhds 0) := by
      have hcont : Filter.Tendsto (fun w : ℂ => f w - f z) (nhds z)
          (nhds (f z - f z)) :=
        hfc_at.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => f z) z)
      simpa only [sub_self] using hcont
    have hlog_tendsto :
        Filter.Tendsto (fun w : ℂ => log (g w / g z)) (nhds z) (nhds 0) := by
      have hcont : Filter.Tendsto (fun w : ℂ => log (g w / g z)) (nhds z)
          (nhds (log (g z / g z))) := hlog.continuousAt
      simpa only [div_self hgz, log_one] using hcont
    have hf_small : ∀ᶠ w in nhds z, ‖f w - f z‖ < Real.pi :=
      by
        simpa [Metric.mem_ball, dist_zero_right] using
          hf_sub_tendsto.eventually (Metric.ball_mem_nhds 0 Real.pi_pos)
    have hlog_small : ∀ᶠ w in nhds z, ‖log (g w / g z)‖ < Real.pi :=
      by
        simpa [Metric.mem_ball, dist_zero_right] using
          hlog_tendsto.eventually (Metric.ball_mem_nhds 0 Real.pi_pos)
    have hU : ∀ᶠ w in nhds z, w ∈ U := hUo.mem_nhds hz
    have heq :
        f =ᶠ[nhds z] fun w : ℂ => f z + log (g w / g z) := by
      filter_upwards [hf_small, hlog_small, hU] with w hfw hlogw hwU
      have hgw : g w ≠ 0 := by
        intro hzero
        exact hg₀ ⟨w, hwU, hzero⟩
      have hfwexp : exp (f w) = g w := by
        simpa [Function.comp_apply] using hfexp hwU
      have hfzexp : exp (f z) = g z := by
        simpa [Function.comp_apply] using hfexp hz
      have hexp : exp (f w - f z) = exp (log (g w / g z)) := by
        rw [exp_sub, hfwexp, hfzexp, exp_log (div_ne_zero hgw hgz)]
      have hleft_im := abs_im_le_norm (f w - f z)
      have hright_im := abs_im_le_norm (log (g w / g z))
      have hleft_abs : |(f w - f z).im| < Real.pi := hleft_im.trans_lt hfw
      have hright_abs : |(log (g w / g z)).im| < Real.pi := hright_im.trans_lt hlogw
      have hsub : f w - f z = log (g w / g z) :=
        exp_inj_of_neg_pi_lt_of_le_pi
          (abs_lt.mp hleft_abs).1 (abs_lt.mp hleft_abs).2.le
          (abs_lt.mp hright_abs).1 (abs_lt.mp hright_abs).2.le hexp
      rw [sub_eq_iff_eq_add] at hsub
      simpa [add_comm] using hsub
    exact (hlog.const_add (f z)).congr_of_eventuallyEq heq
  refine ⟨f, ?_, hfexp, hderiv⟩
  intro z hz
  exact (hderiv z hz).differentiableAt.differentiableWithinAt

end Complex

namespace LeanLab.Riemann

/-- On a simply connected open zero-free domain that avoids its pole, the Riemann zeta function
has a holomorphic logarithm branch with the expected logarithmic derivative. -/
theorem exists_riemannZeta_differentiableLogBranch
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (hone : (1 : ℂ) ∉ U) (hzero : ∀ z ∈ U, riemannZeta z ≠ 0) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧ Set.EqOn (Complex.exp ∘ f) riemannZeta U ∧
        ∀ z ∈ U, HasDerivAt f (deriv riemannZeta z / riemannZeta z) z := by
  apply Complex.exists_differentiableOn_eqOn_exp_comp_of_isSimplyConnected hUc hUo
  · intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      exact hone (h ▸ hz)
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  · rintro ⟨z, hz, hzeta⟩
    exact hzero z hz hzeta

end LeanLab.Riemann
