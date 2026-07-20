# H6 Boyd Normalized Coordinate Loop 23 Preregistration

Date: 2026-07-20

Campaign: `PROOF-ATTEMPT-20260720-H6-BOYD-NORMALIZED-COORDINATE-01`

Mode: `PROOF-ATTEMPT`

Status: `LOCAL_OUTCOME_PROVED / PUBLIC_IMPLEMENTATION_PENDING`

## Opening

RH is the goal. This campaign directly attacks the final normalized-coordinate lift layer of the
current Boyd phase obstruction. A compiled theorem is evidence; a failed attack with a precise
formal obstruction is also a project asset. The compiler decides every claim.

## Selection rationale

- `selected_node`: final residual layer of `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `why_now`: Loop 20 proves properness, Loop 21 proves connectedness and surjectivity, and Loop 22
  proves the punctured phase is a connected degree-two covering with one double branch fiber.
  The highest-value remaining edge is no longer degree computation: it is the actual global
  normalized coordinate and its disk inverse.
- `relation_to_RH`: this coordinate is the change of variables needed to derive the
  inverse-Jacobian adjacent-saddle decomposition underlying the effective `R_2` representation in
  the Polymath H6 route.

## Fixed objects

Retain the compiled definitions

```text
phase(u) = exp(u) - u - 1,
factor(0) = 1,
factor(u) = 2 * phase(u) / u^2          when u != 0,
coordinate(u) = u * principalSqrt(factor(u)),
D = {u : C | |im(u)| < 2*pi and norm(phase(u)) < 2*pi},
B = {z : C | norm(z) < 2*pi}.
```

The intended coordinate target is

```text
W = {w : C | norm(w) < 2 * sqrt(pi)},
q(w) = w^2 / 2,
q(coordinate(u)) = phase(u).
```

## Primary analytic gate

Prove, for every `u in D`, that the removable factor lies in `Complex.slitPlane`:

```text
deBruijnNewmanPolymathBoydComplexSaddleFactor u in Complex.slitPlane.
```

This is the exact condition that makes the already defined principal square-root coordinate
analytic throughout `D`. Numerical probes are discovery aids only and are not evidence. The proof
must derive the no-cut property from the first-strip and phase-disk inequalities or replace it with
an independently compiled global square-root construction.

## Success criteria

The campaign succeeds only if Lean compiles a no-placeholder chain establishing all of the
following, with theorem names allowed to change only for type-correct local design:

1. `factor` is analytic and lies in `Complex.slitPlane` at every point of `D`, or an independently
   constructed normalized square root is analytic on all of `D` and agrees with the Loop 15 local
   branch at the origin.
2. The normalized coordinate restricts to a continuous and analytic map `D -> W`, sends the origin
   to zero, and satisfies `coordinate(u)^2 / 2 = phase(u)` on the actual subtype map.
3. On punctured subtypes, the coordinate is a morphism from the compiled phase covering to the
   standard square covering. It is proper and a local homeomorphism; connectedness then makes it
   surjective, and the two-cardinal fibers make it injective.
4. The coordinate extends to a homeomorphism `D ≃ₜ W` whose inverse agrees near zero with
   `deBruijnNewmanPolymathBoydComplexSaddleLocalInverse` and is analytic on `W`.
5. An aggregate certificate exposes the square identity, homeomorphism, two inverse identities,
   and analytic inverse without assuming Boyd--Nemes equation `(15)`.

## Decision tests

- `PROVED / HARD_GAP_REDUCED`: all success criteria compile and pass the required audits.
- `PARTIAL / OBSTRUCTION_REFINED`: a strict prefix compiles, but the global homeomorphism or
  analytic inverse does not. The attempt log must identify the first missing implication and must
  not relabel the residual node closed.
- `FAILED / COUNTEREXAMPLE`: an exact witness disproves the slit-plane or principal-branch target.
  Record the witness and switch the residual to a nonprincipal global lift.
- `FAILED / LIBRARY_BARRIER`: after testing the direct analytic route and the covering-comparison
  route, the first unavailable theorem or unproved mathematical premise is recorded with exact
  types and experiments. A library inconvenience alone is not a mathematical result.

## Known obstacles before proof editing

- Mathlib supplies the standard punctured power covering and unique lifts from simply connected
  domains, but currently exposes no ready-made classification saying that two connected
  cardinal-two coverings of a punctured disk are equivalent.
- The punctured source and punctured coordinate disk are not simply connected, so the elementary
  simply-connected lifting theorem cannot be applied directly.
- The existing principal coordinate has a global algebraic square identity but is only known
  analytic at the origin and selected adjacent saddles, and continuous on the two compiled radial
  contour lifts. Global continuity must not be inferred from the square identity.
- A degree-two phase map with one double branch fiber does not by itself choose the normalized sign
  or prove agreement with the Loop 15 local inverse.

## Lean surface

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydNormalizedCoordinate.lean`.
- On success or meaningful partial progress, update exact imports and checks in
  `LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`, and
  `LeanLab/Riemann/AxiomsAudit.lean`.
- Update `attempts/h6_polymath_table_row_certificates.md`, `research/hard_gap_dag.md`, and
  `HANDOFF.md` at loop end.

## Mechanical gates

- No `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`, or resource-limit
  relaxation.
- Every promoted declaration must compile independently, appear in exact TargetChecks, and receive
  selected `#print axioms` inspection.
- The production module and full project build must pass before implementation publication.
- Progress claims require the implementation commit and public Lean Action CI evidence.
- This preregistration alone must be committed and pass public CI before any Loop 23 proof-source
  edit.

## Baseline and runtime

- `parent_commit`: `abebcf2801a02d326c66242df4278efff2df73fc`.
- `baseline`: Loop 22 final ledger CI run `29721797207`, build job `88286169619`, passed in `1m46s`.
- `compaction_state`: one inherited compaction summary at the beginning of this continuation; no
  later compaction before preregistration.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active.

## Local outcome

- `result`: `PROVED / HARD_GAP_REDUCED`. Every preregistered endpoint compiles without a
  placeholder.
- `public_preregistration`: commit `02ff528c5ce2a4c63cdd32f8c65238ec795d08d3` passed public Lean
  Action CI run `29722372082`, build job `88287886054`, in `1m32s`, before proof-source editing.
- `implementation`: the 1,184-line production module
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydNormalizedCoordinate.lean` first compiles the complete
  conditional principal-square-root chain under the exact slit-plane premise, then removes that
  premise from the promoted result.
- `global_branch`: Lean proves the removable factor analytic and zero-free on the convex strip
  `|Im u| < 2*pi`. A holomorphic logarithm on this simply connected strip yields a square root
  normalized to one at the origin. Its coordinate squares to the phase and has nonzero derivative
  on the actual phase domain.
- `global_inverse`: local inverse charts and inherited phase properness make the coordinate a
  covering of the natural coordinate disk. A unique covering lift over the contractible disk gives
  a global homeomorphism. The ambient inverse is analytic at every disk point by comparison with
  the local analytic inverse-function branch.
- `germ_compatibility`: the strip square root and the Loop 15 principal square root have the same
  square and value one at zero, so Lean proves they agree eventually at zero. Injectivity of the
  global homeomorphism then proves that the disk inverse agrees eventually with the Loop 15 local
  inverse.
- `aggregate_certificate`:
  `deBruijnNewmanPolymathBoydNormalizedCoordinateGlobalCertificate` packages the square identity,
  both homeomorphism inverse identities, disk-wide analytic inverse, and both germ agreements.
- `mechanical_audit`: the production module, exact Targets, eight exact TargetChecks, eight selected
  axiom prints, forbidden scans, and `git diff --check` pass. Every selected declaration depends
  only on `propext`, `Classical.choice`, and `Quot.sound`. The full project build passes all 8,728
  tasks.
- `obstruction_after`: `OBS-H6-BOYD-COVERING-CERTIFICATE-01` is closed locally. The next exact
  gate is to use the disk-wide analytic inverse and its derivative to derive the inverse-Jacobian
  adjacent-saddle decomposition upstream of Boyd--Nemes equation `(15)`.
- `classification`: source-specific hard-gap reduction plus route infrastructure;
  `rh_frontier_delta=0`, `hard_gap_delta=1`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=1`.
- `runtime`: one inherited compaction summary at Loop 23 start; no later compaction. Exact serving
  model variant, reasoning effort, and serving budget remain unexposed. H6-Q1 and the persistent RH
  Goal remain active.
