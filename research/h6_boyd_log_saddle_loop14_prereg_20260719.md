# H6 Boyd Logarithmic Saddle Integral Loop 14 Preregistration

Date: 2026-07-19

Campaign: `FORMALIZATION-20260719-H6-BOYD-LOG-SADDLE-INTEGRAL-01`

Mode: `LITERATURE`

Status: `LOCAL_SUCCESS / KNOWN_THEOREM_FORMALIZED`

## Exact target

Define, for real `x,u`,

```text
logSaddleIntegrand(x,u) = exp(-x*(exp(u)-u-1)).
```

Prove for every `x>0`:

```text
Integrable (logSaddleIntegrand x)

GammaStar(x)
  = sqrt(x/(2*pi)) * integral_R logSaddleIntegrand(x,u) du,
```

where `GammaStar(x)` is the existing project function
`deBruijnNewmanPolymathScaledGamma (x : C)` and the right side is embedded from `R` into `C`.

## Proposed Lean declarations

```lean
def deBruijnNewmanPolymathBoydLogSaddleIntegrand (x u : R) : R :=
  Real.exp (-x * (Real.exp u - u - 1))

theorem deBruijnNewmanPolymathBoydLogSaddleIntegrand_integrable
    {x : R} (hx : 0 < x) :
    Integrable (deBruijnNewmanPolymathBoydLogSaddleIntegrand x)

theorem deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydLogSaddleIntegral
    {x : R} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : C) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        integral (deBruijnNewmanPolymathBoydLogSaddleIntegrand x) : R) : C)
```

## Derivation and API alignment

Apply the one-dimensional Jacobian theorem on `s=univ` and `f=Real.exp` to the Loop 13
positive-real saddle integrand. Mathlib provides
`integrableOn_image_iff_integrableOn_abs_deriv_smul` and
`integral_image_eq_integral_abs_deriv_smul`. The required geometric facts are

```text
exp '' univ = Ioi 0,
deriv(exp)(u) = exp(u) > 0.
```

For every real `u`, use `log(exp(u))=u` to prove

```text
exp(u) * saddleIntegrand(x,exp(u))
  = exp(-x*(exp(u)-u-1)).
```

This avoids an unproved passage between two endpoint limits: the global measurable-image theorem
performs the change of variables in one kernel-checked step.

## Position in the RH graph

- `node_id`: `H6-Q1`
- `relation_to_RH`: exact steepest-descent coordinate immediately upstream of Boyd's inverse
  saddle and the missing equation `(15)` resurgence decomposition.
- `assumption_frontier_before`: Loop 13 publicly proves the actual project scaled-Gamma
  `t-1-log(t)` saddle representation and integrability for every `x>0`.
- `hard_gap_before`: the logarithmic coordinate, analytic inverse of
  `w^2/2=exp(u)-u-1`, adjacent `2*pi*i` saddle images, Boyd equation `(15)`, effective `R2`, and
  the unconditional Table 1 certificates remain open.

## Success and falsification

- `success_criterion`: both displayed declarations compile for every `x>0` by applying the actual
  one-dimensional Jacobian theorem to the Loop 13 K0 integral; exact witnesses, selected
  standard-only axiom prints, forbidden scans, full build, and public implementation/evidence CI
  pass.
- `falsification_criterion`: the Jacobian weight does not cancel the `/t` factor, the image is not
  exactly `Ioi 0`, or integrability cannot be transported without an extra endpoint premise.
- `proper_prefix_rule`: retain only a compiled global change-of-variables or transformed
  integrability theorem if the final scaled-Gamma rewrite fails. Pointwise phase algebra alone is
  engineering, not campaign success.
- `anti_substitution_rule`: do not assume Boyd/Nemes equation `(15)`, an `R2` estimate, inverse
  saddle analyticity, contour rotation, an unspecified asymptotic, or a replacement Gamma
  function.

## Next decision

- `next_if_success`: preregister the local analytic inverse of
  `w^2/2=exp(u)-u-1`, including normalization at `u=w=0`, before any global branch or adjacent
  saddle-image claim.
- `next_if_blocked`: record whether the failure is image geometry, Jacobian integrability
  transport, or pointwise cancellation and attack that exact lemma.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.

No Loop 14 proof source may be edited before this preregistration passes public Lean Action CI.

Preregistration commit `4d21765574a4e43174a8ace7939ea9d585395d9a` passed public Lean Action CI
run `29661631696`, build job `88125198144`, in `1m31s`. Loop 14 proof-source work was admitted.

## Local outcome

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `production_module`:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydLogSaddleIntegral.lean`
- `compiled_spine`:
  `deBruijnNewmanPolymathBoyd_exp_image_univ`,
  `deBruijnNewmanPolymathBoydLogSaddleIntegrand_eq_jacobian`,
  `deBruijnNewmanPolymathBoydLogSaddleIntegrand_integrable`,
  `integral_deBruijnNewmanPolymathBoydLogSaddleIntegrand`, and
  `deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydLogSaddleIntegral`.
- `assumption_frontier_after`: for every real `x>0`, the exact project scaled-Gamma function now
  has the full-real saddle representation with phase `exp(u)-u-1` as K0. The normalized analytic
  square-root coordinate, its local inverse, adjacent saddle images, equation `(15)`, effective
  `R2`, and all unconditional Table 1 certificates remain open.
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 1
- `engineering_delta`: 0
- `anti_substitution_audit`: no equation `(15)`, `R2` bound, inverse-saddle premise, contour
  rotation, unspecified asymptotic, or replacement Gamma function occurs as a premise.
- `local_mechanical_audit`: standalone compilation, module build, exact Targets, both TargetChecks
  layers, selected axiom prints, empty forbidden scan, and the full 8,719-job build pass. The
  selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `next_exact_gate`: factor the complex phase `exp(u)-u-1` through its double zero at `u=0`,
  construct a local analytic square-root factor `q` with `q(0)=1`, set `w(u)=u*q(u)` so that
  `w(u)^2/2=exp(u)-u-1`, and prove the normalized local analytic inverse at the origin. No global
  branch or adjacent-saddle claim is included yet.
- `compaction_state`: no new compaction detected during Loop 14; the inherited-summary recovery
  audit was completed in Loop 13 and current canonical files remained in context.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
