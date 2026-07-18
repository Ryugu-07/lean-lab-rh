# H6 Boyd Normalized Local Saddle Inverse Loop 15 Preregistration

Date: 2026-07-19

Campaign: `FORMALIZATION-20260719-H6-BOYD-LOCAL-SADDLE-INVERSE-01`

Mode: `LITERATURE`

Status: `PUBLIC_IMPLEMENTATION_PASSED; CLOSURE_EVIDENCE_PENDING`

## Exact target

For complex `u`, define the Boyd saddle phase and its normalized removable factor by

```text
phase(u) = exp(u)-u-1,
factor(0) = 1,
factor(u) = 2*phase(u)/u^2  when u != 0.
```

Define the normalized principal local coordinate

```text
w(u) = u*sqrt(factor(u)).
```

Prove:

```text
factor is analytic at 0,
factor(0)=1,
w is analytic at 0,
w(0)=0,
deriv(w,0)=1,
w(u)^2/2 = exp(u)-u-1  for every complex u.
```

Then define the local inverse supplied by the analytic inverse-function theorem and prove:

```text
uOfW is analytic at 0,
eventually near u=0: uOfW(w(u))=u,
eventually near w=0: w(uOfW(w))=w.
```

## Proposed Lean declarations

```lean
def deBruijnNewmanPolymathBoydComplexSaddlePhase (u : C) : C :=
  Complex.exp u - u - 1

noncomputable def deBruijnNewmanPolymathBoydComplexSaddleFactor (u : C) : C :=
  if u = 0 then 1 else 2 * deBruijnNewmanPolymathBoydComplexSaddlePhase u / u ^ 2

noncomputable def deBruijnNewmanPolymathBoydComplexSaddleCoordinate (u : C) : C :=
  u * Complex.sqrt (deBruijnNewmanPolymathBoydComplexSaddleFactor u)

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_zero :
    AnalyticAt C deBruijnNewmanPolymathBoydComplexSaddleFactor 0

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq :
    forall u : C,
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate u ^ 2 / 2 =
        deBruijnNewmanPolymathBoydComplexSaddlePhase u

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero :
    AnalyticAt C deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0

theorem deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero :
    deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0 = 1

noncomputable def deBruijnNewmanPolymathBoydComplexSaddleLocalInverse : C -> C :=
  -- the local inverse attached to the preceding analytic coordinate

theorem deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_analyticAt_zero :
    AnalyticAt C deBruijnNewmanPolymathBoydComplexSaddleLocalInverse 0

theorem deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_left :
    forall_eventually u near 0,
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse
          (deBruijnNewmanPolymathBoydComplexSaddleCoordinate u) = u

theorem deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_right :
    forall_eventually w near 0,
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydComplexSaddleLocalInverse w) = w
```

Exact filter syntax may follow mathlib notation. The phase, factor normalization, square-root
branch at `1`, derivative normalization, and both local inverse laws are fixed.

## Derivation and audited APIs

The phase is entire and its Taylor coefficients at the origin satisfy

```text
phase(0)=0,
phase'(0)=0,
phase''(0)=1.
```

Apply `AnalyticAt.exists_eq_sum_add_pow_mul` at order three. This yields an analytic `F` with an
exact global identity

```text
phase(u)=u^2/2+u^3*F(u).
```

Hence the piecewise factor agrees everywhere with the analytic function `1+2*u*F(u)`, proving
the removable singularity and normalization without an unproved limit. The principal complex
square root is analytic near `1` because `1` lies in `Complex.slitPlane`; use
`Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane`. Mathlib's
`Complex.cpow_nat_inv_pow` proves the square identity for the principal square root. Finally use
`AnalyticAt.analyticAt_localInverse` and the corresponding strict-derivative eventual left/right
inverse theorems at the nonzero derivative `1`.

## Position in the RH graph

- `node_id`: `H6-Q1`
- `relation_to_RH`: first complex-analytic coordinate needed to pass from the exact Loop 14 saddle
  integral to Boyd's steepest-descent and adjacent-saddle resurgence geometry.
- `assumption_frontier_before`: Loop 14 publicly proves the exact project scaled-Gamma full-real
  saddle integral with phase `exp(u)-u-1` for every positive real parameter.
- `hard_gap_before`: the normalized local inverse, global continuation and branch geometry,
  adjacent `2*pi*i` saddle images, Boyd equation `(15)`, effective `R2`, and the unconditional
  Polymath Table 1 certificates remain open.

## Success and falsification

- `success_criterion`: every fixed declaration above compiles, including the global square
  identity, derivative normalization, analytic local inverse, and both eventual inverse laws;
  exact witnesses, selected standard-only axiom prints, forbidden scans, full build, and public
  implementation/evidence CI pass.
- `falsification_criterion`: the principal square root is not analytic on a neighborhood of the
  normalized factor value, the derivative normalization is not `1`, or the inverse theorem does
  not supply both neighborhood identities without a new premise.
- `proper_prefix_rule`: retain only a compiled analytic removable factor or normalized coordinate
  if a later local-inverse obligation fails. A statement merely recording the double zero or
  Taylor coefficients is engineering, not campaign success.
- `anti_substitution_rule`: do not assume a global inverse, global injectivity, adjacent-saddle
  decomposition, Boyd/Nemes equation `(15)`, an `R2` estimate, contour rotation, or an unspecified
  analytic continuation.

## Next decision

- `next_if_success`: preregister continuation of the local inverse along the two real saddle rays
  and identify the first singular/branch obstruction before attacking adjacent `2*pi*i` images.
- `next_if_blocked`: record whether the failure is Taylor-factor simplification, sqrt analyticity,
  derivative normalization, or inverse-function API alignment and attack that exact obligation.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.

No Loop 15 proof source may be edited before this preregistration passes public Lean Action CI.

## Preregistration evidence

Preregistration commit `8868906756560d3118e5f1d65cbae72dbca1b98c` passed public Lean Action CI
run `29662388346`, build job `88127139991`, in `1m57s`, before the Loop 15 production source was
edited.

## Local outcome

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `production_module`:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydLocalSaddleInverse.lean`
- `compiled_spine`: exact complex phase and first two derivatives at zero; an order-three
  analytic Taylor factor; the piecewise removable factor and its analyticity at zero; the
  normalized principal square-root factor; the coordinate square identity, origin analyticity,
  and unit derivative; a defined local inverse with origin analyticity and both eventual inverse
  laws.
- `assumption_frontier_after`: the normalized local branch at the double saddle is K0. The
  inverse is represented by a total Lean function, but only its origin-neighborhood analytic and
  inverse laws are claimed.
- `hard_gap_after`: global branch continuation, global injectivity, adjacent `2*pi*i` saddle
  images, the Cauchy/resurgence decomposition behind Boyd equation `(15)`, effective `R2`,
  Proposition 6.1/6.3, Table 1 certificates, H6-E/G8, and RH remain open.
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 1
- `engineering_delta`: 0
- `local_mechanical_audit`: standalone source compilation has no diagnostics; `Targets.lean`,
  `TargetChecks.lean`, and `AxiomsAudit.lean` compile; the five selected declarations print only
  `propext`, `Classical.choice`, and `Quot.sound`; all three forbidden scans and
  `git diff --check` are empty; full `lake build` passes with 8,720 jobs.
- `next_exact_gate`: continue the normalized coordinate along the two real saddle rays, prove the
  exact real monotonicity/inverse interface needed for a saddle change of variables, and locate
  the first complex branch obstruction before any adjacent-saddle claim.
- `compaction_state`: one inherited compaction summary was present when Loop 15 proof work
  resumed; the active source, preregistration, governance frontier, and mathlib APIs were
  rechecked before editing.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: V4.1 has no numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.

Implementation commit `016fc4fd71e6b63c142714058547f8b2501fd3a5` passed public Lean Action CI
run `29663109048`, build job `88128987815`, in `1m53s`.
