# H6 Boyd Adjacent Landing and Inverse Jacobian Loop 24 Preregistration

Date: 2026-07-20

Campaign: `PROOF-ATTEMPT-20260720-H6-BOYD-ADJACENT-LANDING-JACOBIAN-01`

Mode: `PROOF-ATTEMPT`

Status: `PUBLICLY_CLOSED`

## Opening

RH is the goal. This campaign directly attacks the adjacent-saddle endpoint that remained open in
Loop 17 and is now unlocked by the global normalized coordinate of Loop 23. Successful compiled
theorems and a precisely recorded failed mechanism are both project assets. The compiler decides
every claim.

## Selection rationale

- `selected_node`: the first inverse-Jacobian and adjacent-critical-image layer of `H6-Q1`,
  immediately downstream of the now-closed `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `why_now`: Loop 23 constructs the actual analytic origin inverse on the full coordinate disk.
  Loops 18 and 19 construct the two adjacent contours and prove that the earlier principal
  coordinate maps them exactly to radial coordinate rays. These are exactly the two inputs absent
  when Loop 17 stopped at a conditional branch theorem.
- `value`: completing the actual landing, derivative, Cauchy-domain, and maximal-radius statements
  fixes the analytic continuation domain upstream of the adjacent-saddle decomposition used in
  Boyd--Nemes equation `(15)`.
- `relation_to_RH`: this is an H6 route bridge toward the effective `R_2` representation consumed
  by the Polymath Proposition 6.1 final-region certificate. It is not itself an RH theorem.

## Fixed objects and notation

Use the compiled objects without redefining them:

```text
phase(u) = exp(u) - u - 1,
D = {u : C | |Im u| < 2*pi and norm(phase(u)) < 2*pi},
W = {w : C | norm(w) < 2*sqrt(pi)},
G : D -> W = the Loop 23 global normalized coordinate homeomorphism,
U : C -> C = deBruijnNewmanPolymathBoydNormalizedCoordinateInverse,
s_n = 2*pi*i*n,
c_n = deBruijnNewmanPolymathBoydComplexSaddleImage n,
rho_n(t) = deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay n t.
```

The ambient function `U` is defined to be zero outside `W`. Therefore no endpoint theorem may
silently evaluate `U(c_1)` or `U(c_-1)`, since those critical images lie on the boundary. Landing
must be stated as a one-sided limit from the open disk.

## Exact mathematical target

Prove all of the following.

1. `U` is analytic on `W`, agrees with the Loop 15 local inverse near zero, and satisfies
   `phase(U(w))=w^2/2` for every `w in W`.
2. On `W`, differentiation of the two inverse identities gives

   ```text
   G'(U(w))*U'(w)=1,
   (exp(U(w))-1)*U'(w)=w,
   U'(0)=1.
   ```

3. For every `0<r<2*sqrt(pi)`, `U'` is represented on `ball 0 r` by its Cauchy power series.
4. For `0<=t<2*pi`, the actual Loop 23 coordinate agrees with the Loop 19 principal coordinate
   along each adjacent contour. Consequently

   ```text
   U(rho_1(t)) = upperContour(t),
   U(rho_-1(t)) = lowerContour(t).
   ```

   Here `upperContour(t)` abbreviates
   `deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)`, and `lowerContour(t)` abbreviates
   `deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t`.
5. Taking `t -> 2*pi` from below yields the two actual branch landing statements

   ```text
   U(rho_1(t))  -> s_1,
   U(rho_-1(t)) -> s_-1.
   ```

6. If `V` is analytic on a centered disk of radius `R`, agrees near zero with the Loop 15 local
   inverse, and `R>2*sqrt(pi)`, then the identity theorem makes `V=U` on `W`; continuity and the
   two landing paths force `V(c_n)=s_n` for `n=1` or `n=-1`. The compiled Loop 17 endpoint
   obstruction then gives `R<=2*sqrt(pi)`, a contradiction. Equivalently, every such analytic
   continuation has radius at most `2*sqrt(pi)`.

## Proposed Lean declarations

Exact helper names may change for type-correct local design, but the promoted quantifiers and
mathematical content are fixed.

```lean
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticOnNhd :
    AnalyticOnNhd C deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
      deBruijnNewmanPolymathBoydOpenCoordinateDisk

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_phase
    {w : C} (hw : w in deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) = w ^ 2 / 2

theorem deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_mul
    {w : C} (hw : w in deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) *
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w = 1

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverseJacobian_phase
    {w : C} (hw : w in deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) - 1) *
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w = w

theorem deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero :
    deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse 0 = 1

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverseJacobian_hasCauchyPowerSeriesOnBall
    {r : NNReal} (hr0 : 0 < r)
    (hr : (r : R) < 2 * Real.sqrt Real.pi) :
    HasFPowerSeriesOnBall
      (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse)
      (cauchyPowerSeries
        (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) 0 r)
      0 r

theorem deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_upper
    {t : R} (ht0 : 0 <= t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t

theorem deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_lower
    {t : R} (ht0 : 0 <= t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t) =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper
    {t : R} (ht0 : 0 <= t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower
    {t : R} (ht0 : 0 <= t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
      deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t

theorem tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper :
    Tendsto
      (fun t : R => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t))
      (nhdsWithin (2 * Real.pi) (Set.Iio (2 * Real.pi)))
      (nhds (deBruijnNewmanPolymathBoydComplexSaddlePoint 1))

theorem tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower :
    Tendsto
      (fun t : R => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t))
      (nhdsWithin (2 * Real.pi) (Set.Iio (2 * Real.pi)))
      (nhds (deBruijnNewmanPolymathBoydComplexSaddlePoint (-1)))

theorem deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent_unconditional
    {V : C -> C} {R : R}
    (hR : 0 < R)
    (hV : AnalyticOnNhd C V (Metric.ball 0 R))
    (hlocal : V =f[nhds 0]
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse) :
    R <= 2 * Real.sqrt Real.pi
```

The final theorem is intentionally unconditional on an endpoint equality. Its proof must derive
the endpoint equality from the compiled radial landing and the identity theorem before invoking
the Loop 17 conditional obstruction.

## Proof strategy fixed before editing

1. Promote Loop 23 pointwise analyticity to `AnalyticOnNhd`, compose the homeomorphism inverse
   identity with the global coordinate square identity, and differentiate both inverse equations.
2. Instantiate the generic Loop 17 Cauchy theorem with the actual `U`; no new Cauchy machinery is
   to be invented if the existing theorem type applies.
3. For each adjacent contour, prove membership in `D` for `0<=t<2*pi`. The phase-norm condition is
   exact from the contour equation. Strict strip membership follows from the Loop 18 parameter
   range and strictness away from the terminal value.
4. The global and principal coordinates have equal squares along a contour. Their germs agree near
   zero by Loop 23. Propagate the sign along a nonzero compact subinterval using
   `IsPreconnected.eq_of_sq_eq`; handle `t=0` separately. This avoids assuming a global principal
   square-root cut condition.
5. Apply the global homeomorphism inverse identity to obtain the two radial inverse formulas, then
   rewrite the already compiled Loop 18 endpoint limits.
6. For a hypothetical larger analytic branch `V`, use analytic identity on the connected open
   disk `W` to prove `V=U` there. Pass to the endpoint along either radial ray by continuity of
   `V`, then apply
   `deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent`.

## Success, falsification, and local stop

- `success_criterion`: all six exact target blocks compile, including both actual radial landings
  and the unconditional maximal-radius theorem. Exact Targets/TargetChecks, selected standard-only
  axiom prints, forbidden scans, the full build, and public implementation/evidence CI pass.
- `falsification_criterion`: a compiled witness shows that the Loop 23 normalized coordinate takes
  the opposite sign from the Loop 19 coordinate on an adjacent contour; an interior contour point
  lies outside `D`; the actual inverse has a different adjacent radial limit; or a compiled larger
  analytic branch agrees with the origin germ.
- `partial_criterion`: retain only a strict, mathematically meaningful prefix such as the complete
  derivative/Cauchy certificate or one full contour-to-landing chain. Record the first missing
  theorem as a new obstruction. Isolated continuity, interval-membership, or derivative helper
  lemmas do not qualify as loop progress.
- `local_stop`: stop this campaign when the full endpoint is proved, a falsification witness
  compiles, or the first genuinely external mathematical obstruction is isolated after both the
  contour sign-propagation and analytic-identity routes have been attempted. Local stop returns to
  value-ranked route selection and never pauses the persistent RH Goal.

## Assumption frontier and novelty audit

- `assumption_frontier_before`: K0 contains the actual homeomorphism `D ~= W`, its analytic ambient
  inverse `U`, both inverse identities, germ compatibility with Loop 15, the two adjacent contour
  lifts and endpoint limits, their principal-coordinate radial identities, and the Loop 17
  conditional radius obstruction.
- `hard_gap_before`: no theorem yet connects the Loop 23 global coordinate to the Loop 19 contour
  coordinate away from the origin; therefore the actual inverse radial landing and the
  unconditional maximal centered radius remain open. The actual inverse Jacobian has not yet been
  exposed as a Cauchy series.
- `nearest_project_attempt`: Loop 17 proves only a generic branch phase/Cauchy theorem and a radius
  bound conditional on endpoint landing. Loop 23 supplies the missing disk-wide analytic branch.
- `material_difference_from_loop17`: this attack no longer tries to construct a branch from
  critical-value exclusion. It starts from a compiled global homeomorphism and must discharge the
  previously explicit landing premise through the separately compiled Loop 18/19 contours.
- `closest_primary_literature`: W. G. C. Boyd, *Gamma function asymptotics by an extension of the
  method of steepest descents*, Proc. R. Soc. Lond. A 447 (1994), especially equations `(2.14)` and
  `(4.2)` as cited by Nemes; Boyd's 1995 open exposition of Conditions 2.1; and G. Nemes,
  arXiv `1310.0166`, equation `(15)`.
- `source_boundary`: equation `(15)`, its Stieltjes integrals, and any effective `R_2` estimate are
  downstream and may not be assumed in this loop.
- `conjecture_status`: no model-original conjecture is admitted or used as a premise.

## Lean surface and mechanical gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentLandingJacobian.lean`.
- On success or meaningful partial progress, update exact imports and witnesses in
  `LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`, and
  `LeanLab/Riemann/AxiomsAudit.lean`.
- At loop end update `attempts/h6_polymath_table_row_certificates.md`,
  `research/hard_gap_dag.md`, and `HANDOFF.md`.
- No `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`, or resource-limit
  relaxation.
- Every promoted theorem must compile independently and receive an exact statement witness and
  selected `#print axioms` inspection.
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 24
  Lean proof-source edit.

## Baseline and runtime

- `parent_commit`: `6c0289474b7a144deec70e2be186a6f136e4505b`.
- `baseline`: Loop 23 final ledger CI run `29725210457`, build job `88296608181`, passed in
  `1m29s`.
- `compaction_state`: one inherited compaction summary at Loop 24 start; canonical governance,
  `HANDOFF.md`, `Targets.lean`, `TargetChecks.lean`, the current attempt, hard-gap DAG, Loop 17 and
  Loop 23 preregistrations, and the relevant production modules were re-read before selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active.

## Next decision

- `next_if_success`: derive the two adjacent inverse-Jacobian singular contributions and compare
  their exact Cauchy/discontinuity formula with Boyd--Nemes equation `(15)` at `N=2`.
- `next_if_blocked`: record the first failed equality or continuation step with its exact Lean
  type, then compare direct boundary-germ/Stieltjes extraction with a repaired contour argument.
- `global_goal`: the persistent RH Goal remains active in every local outcome.

## Local outcome

- `result`: `PROVED / HARD_GAP_REDUCED`. Every preregistered mathematical endpoint compiles.
- `production_module`:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentLandingJacobian.lean`, 691 lines.
- `actual_branch`: the Loop 23 ambient inverse is analytic on the complete coordinate disk,
  satisfies `phase(U(w))=w^2/2`, and has both the global-coordinate inverse derivative identity
  and `(exp(U(w))-1)*U'(w)=w`; Lean also proves `U'(0)=1`.
- `cauchy_domain`: the generic Loop 17 theorem is instantiated without a new premise, giving the
  Cauchy power series of `U'` on every radius `0<r<2*sqrt(pi)`.
- `sign_and_landing`: both Loop 18 contours lie strictly in the source phase domain before their
  terminal parameter. The Loop 23 global coordinate and Loop 19 principal coordinate have equal
  squares; germ equality supplies a positive anchor, and `IsPreconnected.eq_of_sq_eq` propagates
  the sign on every compact nonzero interval. The homeomorphism inverse then identifies both
  radial lifts and proves their one-sided limits at `s_1` and `s_-1`.
- `maximal_radius`: any larger centered analytic continuation agrees with `U` on the first disk by
  the analytic identity theorem. Continuity along the upper radial ray forces its boundary value
  to be `s_1`, so the Loop 17 critical-derivative obstruction gives the contradiction. The final
  radius theorem has no landing premise.
- `aggregate_certificate`:
  `deBruijnNewmanPolymathBoydAdjacentLandingJacobianCertificate`.
- `mechanical_audit`: the production module, `Targets.lean`, exact `TargetChecks.lean`, and
  `AxiomsAudit.lean` compile. Eighteen selected new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. Placeholder, custom-declaration, and resource-relaxation
  scans are empty; `git diff --check` passes; the full build passes all 8,729 tasks.
- `classification`: source-specific hard-gap reduction plus route infrastructure;
  `rh_frontier_delta=0`, `hard_gap_delta=1`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=0`.
- `public_preregistration`: commit `a0443b921a48072d889402737c6d38a468eeab71` passed public Lean
  Action CI run `29725851711`, build job `88298656245`, in `1m56s` before proof-source editing.
- `public_implementation`: commit `e8ee2a1997a66289459fa7bb0ee1ac7eec3bcef9` passed public
  Lean Action CI run `29727609529`, build job `88304224149`, in `1m58s`.
- `public_closure`: evidence commit `fc4b716a537448d0630d939cfec44335f6eaaa58` passed public
  Lean Action CI run `29727795315`, build job `88304816776`, in `2m6s`.
- `next_exact_gate`: derive the two adjacent inverse-Jacobian singular contributions and prove the
  source-exact Boyd--Nemes equation `(15)` at `N=2`; equation `(15)` and effective `R_2` remain
  unproved and are not premises.
- `runtime`: one inherited compaction summary at Loop 24 start followed by the required canonical
  reread, and a second inherited summary during integration after the local build and initial log
  edits. Canonical governance, `HANDOFF.md`, Targets/TargetChecks, AxiomsAudit, the current attempt,
  hard-gap DAG, and this preregistration were re-read again before the implementation commit.
  Exact serving model variant, reasoning effort, and serving budget remain unexposed. H6-Q1 and
  the persistent RH Goal remain active.
