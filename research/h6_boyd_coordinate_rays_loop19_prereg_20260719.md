# H6 Boyd Coordinate Rays Loop 19 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-COORDINATE-RAYS-01`

Mode: `PROOF-ATTEMPT`

Status: `PROVED / KNOWN_THEOREM_FORMALIZED`

## Target

- `node_id`: residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `relation_to_RH`: boundary path-lifting layer between the Boyd normalized saddle coordinate and
  the `R_2` representation used by the Polymath final-region certificate.

Let `W(u)` be the compiled normalized principal Boyd coordinate, let `C_+(t)` be the Loop 18 upper
contour point with phase `-i*t`, and let `C_-(t)` be the lower contour point with phase `i*t`, for
`0 <= t <= 2*pi`. Let `A_n=W(2*pi*i*n)` be the compiled critical image. Define the radial segment

```text
radial(n,t) = (sqrt(t) / sqrt(2*pi)) * A_n.
```

Prove first that the removable factor under the principal square root remains in the closed right
half-plane along both contour lifts:

```text
0 <= re(factor(C_+(t))),
0 <= re(factor(C_-(t))).
```

This must be derived from the exact quotient

```text
factor(u) = 2*phase(u)/u^2
```

and the Loop 18 signs, not postulated as a branch condition. Deduce that both composed coordinate
lifts are continuous on `[0,2*pi]`, despite the fact that the global principal complex square root
is discontinuous across the negative real axis.

Then prove the exact radial identities

```text
W(C_+(t)) = radial(1,t),
W(C_-(t)) = radial(-1,t)
```

for every `t` in `[0,2*pi]`. In particular the actual normalized coordinate, not merely its square,
must carry the two Loop 18 adjacent contours onto the two radial segments ending at `A_1` and
`A_-1`.

This target supplies explicit one-dimensional inverse lifts for both critical rays. It does not
assert that the region between the contours covers the disk, does not exclude an interior
asymptotic singularity, and does not construct a disk-wide analytic inverse.

## Proposed Lean declarations

Exact helper names may vary while preserving the endpoint statements.

```lean
noncomputable def deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
    (n : Z) (t : R) : C :=
  ((Real.sqrt t / Real.sqrt (2 * Real.pi) : R) : C) *
    deBruijnNewmanPolymathBoydComplexSaddleImage n

noncomputable def deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift
    (t : R) : C :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))

noncomputable def deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift
    (t : R) : C :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)

theorem deBruijnNewmanPolymathBoydAdjacentContourUpper_factor_re_nonneg
    {t : R} (ht : t in Set.Icc 0 (2 * Real.pi)) :
    0 <= (deBruijnNewmanPolymathBoydComplexSaddleFactor
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))).re

theorem deBruijnNewmanPolymathBoydAdjacentContourLower_factor_re_nonneg
    {t : R} (ht : t in Set.Icc 0 (2 * Real.pi)) :
    0 <= (deBruijnNewmanPolymathBoydComplexSaddleFactor
      (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)).re

theorem continuousOn_deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift :
    ContinuousOn deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift
      (Set.Icc 0 (2 * Real.pi))

theorem continuousOn_deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift :
    ContinuousOn deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift
      (Set.Icc 0 (2 * Real.pi))

theorem deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_eq_radialRay
    {t : R} (ht : t in Set.Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift t =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t

theorem deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_eq_radialRay
    {t : R} (ht : t in Set.Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift t =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t
```

The pseudocode uses ASCII type names and relations only for portability. Production statements
will use exact Lean syntax.

## Success and falsification

- `success_criterion`: both factor real-part inequalities, both coordinate-lift continuity
  theorems, exact radial-ray square and endpoint identities, and both full interval radial
  identities compile. Exact Targets/TargetChecks, selected standard-only axiom prints, forbidden
  scans, full build, and public implementation/evidence CI must pass.
- `falsification_criterion`: the factor crosses the negative real axis; either principal
  coordinate lift is discontinuous; the coordinate chooses the opposite radial square root on a
  nonempty subinterval; or an endpoint fails to equal the compiled adjacent critical image.
- `proper_prefix_rule`: if a final radial identity is blocked, retain results only if Lean proves
  the factor half-plane statement and coordinate-lift continuity for both contours together with
  the exact common-square and endpoint data. Pointwise phase squares alone repeat Loop 18 and do
  not qualify.
- `anti_substitution_rule`: do not assume principal-square-root continuity, factor slit-plane
  membership, either radial identity, a global coordinate branch, a disk inverse, absence of
  asymptotic values, or Boyd--Nemes equation `(15)`.

## Prior state and attack angle

- `assumption_frontier_before`: Loop 17 gives the exact adjacent critical images and the
  conditional radius obstruction. Loop 18 gives both explicit phase contours, their unique phase
  lifts, and landing at `+/-2*pi*i`. All are public K0.
- `hard_gap_before`: the phase contours have not been shown to be lifts of radial paths for the
  actual normalized principal coordinate; the two-dimensional covering and no-asymptotic-value
  certificate remain open.
- `known_obstacles`: `Complex.sqrt` is not globally continuous across the negative real axis, so
  equality of coordinate squares does not determine the sign. At `t=0` the radial comparison
  vanishes, preventing a direct division argument on the whole closed interval.
- `nearest_primary_source`: Boyd 1995 Conditions 2.1 and the Gamma adjacent-saddle discussion at
  `https://intlpress.com/site/pub/files/_fulltext/journals/maa/1995/0002/0004/MAA-1995-0002-0004-a007.pdf`;
  Boyd 1994, DOI `10.1098/rspa.1994.0158`; Nemes arXiv `1310.0166`, equation `(15)`.
- `nearest_project_attempt`: Loops 17 and 18, especially
  `K0-H6-BOYD-ADJACENT-CONTOURS-01` and residual
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `new_attack_angle`: compute the real part of `2*phase(u)/u^2` along the already constructed
  contour and prove it is nonnegative. Then use `IsPreconnected.eq_of_sq_eq` on each interval
  `[t,2*pi]`, seeded at the actual critical image endpoint, to prevent a square-root sign switch.
  This attacks normalized-coordinate branch consistency rather than phase geometry alone.

## Audited proof skeleton

1. For the upper lift write `u=x+i*y`, with `x<=0`, `y>=0`, and `phase(u)=-i*t`. Away from
   `u=0`, expand `re(2*phase(u)/u^2)` as a nonnegative quotient proportional to `-t*x*y`.
2. Treat `u=0` with the removable factor value `1`. Repeat for the lower lift, or derive the
   corresponding sign directly from `phase(u)=i*t` and `im(u)<=0`.
3. Compose factor continuity at zero and away from zero with `Complex.continuousAt_sqrt`, using
   the proved closed-right-half-plane condition. Obtain continuity of both coordinate lifts on
   the entire closed interval.
4. Prove that each coordinate lift and its radial candidate have the same square. Prove the
   radial candidate is nonzero on every interval `[t,2*pi]` with `t>0`.
5. At `2*pi`, the radial candidate is definitionally the compiled critical image. Apply
   `Set.IsPreconnected.eq_of_sq_eq` on `[t,2*pi]` to propagate the endpoint sign to every `t>0`.
   Handle `t=0` from the compiled origin values.

## Runtime and gate

- `compaction_state`: no new compaction after Loop 18 closure. Current governance, HANDOFF,
  Targets/TargetChecks, the current attempt, hard-gap DAG, Loop 17/18 sources, and relevant
  mathlib square-root/preconnected APIs were re-read before this preregistration.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no V4.1 numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
- `previous_public_ledger`: Loop 18 ledger commit
  `144efe9c47a414741a22cda807d10f55480fa68b` passed public Lean Action CI run `29667399367`,
  build job `88140167965`, in `1m31s`.

No Loop 19 Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Outcome

- `result`: `PROVED / KNOWN_THEOREM_FORMALIZED`. The complete preregistered endpoint compiles.
- `implementation`: the 378-line production module
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydCoordinateRays.lean` proves the generic identity
  `re(factor(u))=4*s*re(u)*im(u)/normSq(u^2)` when `phase(u)=s*i`, then combines it with the
  Loop 18 contour signs.
- `compiled_spine`: factor real part nonnegative along both contour lifts; continuity of the actual
  principal coordinate on both closed intervals; exact common-square formulas; exact origin and
  adjacent-critical-image endpoints; nonvanishing radial candidates away from zero; preconnected
  sign propagation; both radial identities; and both norm-square formulas `norm^2=2*t`.
- `mechanical_audit`: the source, `Targets.lean`, eight exact `TargetChecks.lean` witnesses, and
  eight selected `AxiomsAudit.lean` prints compile. Every selected print contains only `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden-token, custom-declaration, and resource-option
  scans are empty; `git diff --check` passes; the full build passes 8,724 jobs.
- `obstruction_after`: the normalized-coordinate branch-consistency and boundary radial-lift layer
  of `OBS-H6-BOYD-COVERING-CERTIFICATE-01` is closed. The residual obstruction is entirely
  two-dimensional: define the origin saddle component bounded by these lifts, rule out interior
  escape/asymptotic singularities over the open target disk, and prove proper covering/path
  lifting for the disk-wide analytic inverse.
- `classification`: known theorem formalized plus route infrastructure;
  `rh_frontier_delta=0`, `hard_gap_delta=0`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=1`.
- `public_preregistration`: commit `17000cb4a3a9b1eabada3fd35ea4d744fe5520fb` passed public Lean
  Action CI run `29667732245`, build job `88141103415`, in `1m35s`, before source editing.
- `public_implementation`: commit `7efc4496c89badf7182f6fc6fe81734bb8782924` passed public Lean
  Action CI run `29668228884`, build job `88142434731`, in `2m22s`.
- `runtime`: no new compaction. Exact serving model variant, reasoning effort, and serving budget
  remain unexposed; V4.1 imposes no numerical quota.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
