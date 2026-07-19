# H6 Boyd Adjacent Contour Loop 18 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-ADJACENT-CONTOUR-01`

Mode: `PROOF-ATTEMPT`

Status: `PROVED / KNOWN_THEOREM_FORMALIZED`

## Target

- `node_id`: `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `relation_to_RH`: bridge from the Boyd saddle geometry to the `R_2` representation used by the
  Polymath final-region certificate.

Write

```text
phase(u) = exp(u) - u - 1.
```

For real `x,y`, the equation that the phase at `u=x+i*y` has zero real part is

```text
exp(x) * cos(y) = x + 1.                                      (C)
```

For every real `y`, prove that `(C)` has a unique solution `x(y)` in `[-2,0]`. On the source
interval `0 <= y <= 2*pi`, prove

```text
x(0) = 0,
x(2*pi) = 0,
x(y) < 0                    when 0 < y < 2*pi.
```

Define the positive adjacent contour and its phase-height parameter by

```text
gammaPlus(y) = x(y) + i*y,
q(y) = exp(x(y)) * sin(y) - y.
```

Prove that `gammaPlus` is continuous on `[0,2*pi]`, differentiable on `(0,2*pi)`, and

```text
re (phase (gammaPlus(y))) = 0,
im (phase (gammaPlus(y))) = q(y),
gammaPlus(0) = 0,
gammaPlus(2*pi) = 2*pi*i.
```

On the open interval, derive the exact implicit and phase-height derivatives

```text
x'(y) = exp(x(y)) * sin(y) / x(y),
q'(y) = (x(y)^2 + exp(2*x(y))*sin(y)^2) / x(y) < 0.
```

Conclude that `q` is continuous and strictly decreasing from `0` to `-2*pi`. Hence every
`s` in `[-2*pi,0]` has a unique lift on this contour, and the inverse phase lift tends to
`2*pi*i` as `s` tends to `-2*pi` from above. Obtain the negative adjacent contour and landing at
`-2*pi*i` by complex conjugation.

This target constructs the two explicit adjacent steepest-descent boundary paths required by
Boyd's geometric conditions. It does not assert the two-dimensional saddle domain is a covering
space, does not construct the disk-wide inverse branch, and does not assume Boyd--Nemes equation
`(15)`.

## Proposed Lean declarations

Exact implementation names may be split while preserving these statements.

```lean
def deBruijnNewmanPolymathBoydAdjacentContourEquation (x y : R) : R :=
  Real.exp x * Real.cos y - x - 1

theorem existsUnique_deBruijnNewmanPolymathBoydAdjacentContourRealPart
    (y : R) :
    exists unique x : R,
      x in Set.Icc (-2) 0 and
      deBruijnNewmanPolymathBoydAdjacentContourEquation x y = 0

noncomputable def deBruijnNewmanPolymathBoydAdjacentContourRealPart (y : R) : R :=
  choose the preceding unique root

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_mem (y : R) :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart y in Set.Icc (-2) 0

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_eq (y : R) :
    Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.cos y =
      deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_neg
    {y : R} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart y < 0

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourRealPart :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourRealPart

theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourRealPart
    {y : R} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourRealPart
      (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
        deBruijnNewmanPolymathBoydAdjacentContourRealPart y) y

def deBruijnNewmanPolymathBoydAdjacentContourPlus (y : R) : C :=
  deBruijnNewmanPolymathBoydAdjacentContourRealPart y + y * I

def deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight (y : R) : R :=
  Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y - y

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPlus (y : R) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentContourPlus y) =
      deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y * I

theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
    {y : R} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
      ((deBruijnNewmanPolymathBoydAdjacentContourRealPart y)^2 +
        Real.exp (2 * deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
          Real.sin y ^ 2) /
        deBruijnNewmanPolymathBoydAdjacentContourRealPart y y

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_strictAntiOn :
    StrictAntiOn deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
      (Set.Icc 0 (2 * Real.pi))

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_endpoints :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight 0 = 0 and
      deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight (2 * Real.pi) =
        -2 * Real.pi

theorem existsUnique_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift
    {s : R} (hs : s in Set.Icc (-2 * Real.pi) 0) :
    exists unique y : R,
      y in Set.Icc 0 (2 * Real.pi) and
      deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y = s

theorem tendsto_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_at_neg_two_pi :
    Tendsto deBruijnNewmanPolymathBoydAdjacentContourPhaseLift
      (nhdsWithin (-2 * Real.pi) (Set.Ioi (-2 * Real.pi)))
      (nhds (2 * Real.pi * I))
```

The pseudocode uses ASCII words for binders and conjunctions only to keep the preregistration
portable. Production declarations will use exact Lean syntax and may package the last inverse as
an order anti-isomorphism.

## Success and falsification

- `success_criterion`: construct the unique root globally, prove its continuity and interior
  derivative, prove the exact complex phase identity, strict phase-height decrease and endpoints,
  construct the unique interval phase lift, and prove both adjacent landing statements. Exact
  Targets/TargetChecks, selected standard-only axiom prints, forbidden scans, full build, and
  public implementation/evidence CI must pass.
- `falsification_criterion`: equation `(C)` has more than one root in `[-2,0]`; its selected root
  fails continuity; the phase height is not strictly decreasing; an endpoint differs from
  `0` or `+/-2*pi*i`; or the derivative formula has a different sign or normalization.
- `proper_prefix_rule`: if the inverse phase lift is blocked, retain results only if Lean compiles
  the unique root, its continuity, exact zero-real-phase contour, endpoint values, and strict
  phase-height monotonicity. If continuity or monotonicity is blocked, record the first exact
  topological or implicit-function goal as a new `OBS`; isolated trigonometric identities or root
  bounds alone do not qualify.
- `anti_substitution_rule`: do not postulate root continuity, a path lift, monotonicity, the Boyd
  saddle domain, a covering map, absence of asymptotic values, the disk-wide inverse, either
  landing statement, or equation `(15)`.

## Prior state and attack angle

- `assumption_frontier_before`: Loop 17 gives all phase critical points, exact adjacent critical
  image radii, generic analytic-branch phase propagation and Cauchy expansions, plus the adjacent
  radius obstruction under explicit landing. All are public K0.
- `hard_gap_before`: no explicit adjacent contour, no phase lift to either adjacent saddle, no
  saddle-domain covering theorem, no exclusion of asymptotic singularities, and no disk inverse.
- `known_obstacles`: the partial derivative of `(C)` with respect to `x` equals the selected root
  at a solution, so the ordinary implicit-function theorem degenerates at both endpoints. The
  interior derivative is nondegenerate, but global continuity and endpoint control require a
  compact uniqueness argument or a separate monotone-root theorem.
- `nearest_primary_source`: Boyd's open 1995 primary exposition, Conditions 2.1 and its Gamma
  section, at
  `https://intlpress.com/site/pub/files/_fulltext/journals/maa/1995/0002/0004/MAA-1995-0002-0004-a007.pdf`;
  Boyd 1994, DOI `10.1098/rspa.1994.0158`; Nemes arXiv `1310.0166`, equation `(15)`.
- `nearest_project_attempt`: Loop 17 and `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `new_attack_angle`: replace the missing two-dimensional covering theorem by the explicit real
  graph of the adjacent zero-real-phase contour. The identity
  `exp(x(y))*cos(y)=x(y)+1` turns the implicit derivative denominator into `x(y)`, and therefore
  turns the phase-height derivative into a manifestly negative quotient on the open interval.

## Audited proof skeleton

1. At `x=-2`, the contour equation is positive because
   `1-exp(-2)>0`; at `x=0` it is `cos(y)-1<=0`. Apply IVT.
2. On `[-2,0]`, the `x` derivative is `exp(x)*cos(y)-1`; it is strictly negative in the interior,
   giving uniqueness.
3. Obtain global root continuity from compact interval containment plus uniqueness, or from a
   mathlib continuous-root theorem if an exact match exists.
4. On `0<y<2*pi`, prove `cos(y)<1`, hence `x(y)<0`; apply the implicit-function theorem locally
   and use uniqueness to identify the local branch with the global selected root.
5. Differentiate `q`; rewrite `exp(x)*cos(y)-1` as `x` using `(C)` and prove the displayed
   negative formula.
6. Combine interior derivative negativity with continuity and endpoint values to get strict
   antitonicity and a unique interval inverse. Use conjugation for the lower contour.

## Runtime and gate

- `compaction_state`: Loop 18 starts after an inherited compaction summary; canonical governance,
  HANDOFF, Targets, TargetChecks, the active attempt log, hard-gap DAG, and Loop 17 outcome were
  re-read before this preregistration.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no V4.1 numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
- `previous_public_ledger`: Loop 17 ledger commit
  `c7eece5cb1ffaab970c6a4af0643c3f1f2f234fe` passed public Lean Action CI run `29666322004`,
  build job `88137224007`, in `1m30s`.

No Loop 18 Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Outcome

- `result`: `PROVED / KNOWN_THEOREM_FORMALIZED`. The complete preregistered endpoint compiles.
- `implementation`: the 673-line production module
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentContour.lean` represents the root by the
  inverse of the strict carrier `h(x)=(x+1)*exp(-x)` on `x<=0`. This proves global continuity
  without assuming endpoint implicit regularity.
- `compiled_spine`: unique root in `[-2,0]`, global root continuity, exact interior root
  derivative, exact upper complex phase identity, the manifestly negative phase-height
  derivative, strict antitonicity on `[0,2*pi]`, endpoint values, a unique interval phase lift,
  the upper landing at `2*pi*i`, and the conjugate lower lift and landing at `-2*pi*i`.
- `mechanical_audit`: the source, `Targets.lean`, ten exact `TargetChecks.lean` witnesses, and
  nine selected `AxiomsAudit.lean` prints compile. Every selected print contains only `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden-token, custom-declaration, and resource-option
  scans are empty; `git diff --check` passes; the full build passes 8,723 jobs.
- `obstruction_after`: the adjacent-boundary and one-dimensional landing layer of
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01` is closed. The residual obstruction is two-dimensional:
  prove that the two contours bound the origin saddle component, establish phase-specific path
  lifting/properness with no asymptotic singularities over the target disk, and construct the
  disk-wide analytic inverse.
- `classification`: known theorem formalized plus route infrastructure;
  `rh_frontier_delta=0`, `hard_gap_delta=0`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=1`.
- `public_preregistration`: commit `54d120eab46217730506e334e24d27aea25da472` passed public Lean
  Action CI run `29666526948`, build job `88137742671`, in about `2m12s`, before source editing.
- `public_implementation`: commit `3b2e050eaab55c41a2f9dc5fffa88e173b284f89` passed public Lean
  Action CI run `29667229566`, build job `88139688107`, in `2m22s`.
- `runtime`: a second inherited compaction summary occurred during integration; canonical
  governance, HANDOFF, Targets, TargetChecks, this attempt, the hard-gap DAG, and this
  preregistration were re-read afterward. Exact serving model variant, reasoning effort, and
  serving budget remain unexposed; V4.1 imposes no numerical quota.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
