# H6 Boyd Phase-Domain Connectedness Loop 21 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-PHASE-DOMAIN-CONNECTEDNESS-01`

Mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED / PUBLIC_CI_PENDING`

## Target

- `node_id`: residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `relation_to_RH`: this is the connected-origin-component and surjectivity layer required before
  the proper Boyd phase map can be assigned its branched degree and lifted to the normalized
  coordinate inverse used in the `R_2` representation feeding the Polymath final-region
  certificate.

Retain the Loop 20 definitions

```text
phase(u) = exp(u) - u - 1,
D = {u : C | |im(u)| < 2*pi and norm(phase(u)) < 2*pi},
B = {z : C | norm(z) < 2*pi},
Phi : D -> B.
```

Prove that `phase(u)=0` and `|im(u)|<2*pi` imply `u=0`. Prove that the global phase is an open map
and hence that `Phi` is an open map. Combine the singleton zero fiber with Loop 20 properness and
the connected-components cardinal theorem for open and closed maps to prove that `D` is connected.
Finally prove that `Phi` is surjective by showing its range is a nonempty clopen subset of the
connected target disk.

This campaign does not assume or claim that every nonzero phase fiber has exactly two points, that
the phase map has branched degree two, that `D` is simply connected, that the normalized coordinate
is globally injective, or that Boyd--Nemes equation `(15)` already holds.

## Proposed Lean declarations

Exact helper names may vary while preserving the four final statements.

```lean
theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff_of_abs_im_lt_two_pi
    {u : C} (hu : |u.im| < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase u = 0 <-> u = 0

theorem isOpenMap_deBruijnNewmanPolymathBoydComplexSaddlePhase :
    IsOpenMap deBruijnNewmanPolymathBoydComplexSaddlePhase

theorem isOpenMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    IsOpenMap deBruijnNewmanPolymathBoydPhaseOnOriginDomain

theorem isConnected_deBruijnNewmanPolymathBoydOriginPhaseDomain :
    IsConnected deBruijnNewmanPolymathBoydOriginPhaseDomain

theorem surjective_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    Function.Surjective deBruijnNewmanPolymathBoydPhaseOnOriginDomain
```

The pseudocode uses ASCII connectives only for portability. Production statements will use exact
Lean syntax.

## Success and falsification

- `success_criterion`: the strip zero classification, both open-map statements, connectedness of
  the actual Loop 20 source subtype, and surjectivity onto the actual target subtype all compile.
  Exact Targets/TargetChecks, selected standard-only axiom prints, forbidden scans, full build,
  and public implementation/evidence CI must pass.
- `falsification_criterion`: a nonzero `u` with `|im(u)|<2*pi` and `phase(u)=0`; failure of global
  holomorphic openness; more than one connected component of `D`; or a target value in `B` absent
  from the phase image.
- `proper_prefix_rule`: if source connectedness or surjectivity is blocked, retain the unique-zero
  theorem and open-map theorem only if both exact global statements compile and the first missing
  topology interface is recorded as an obstruction. A real-only zero theorem or a generic clopen
  lemma detached from the actual subtypes does not qualify.
- `anti_substitution_rule`: do not assume source connectedness, singleton zero fiber, surjectivity,
  fiber cardinality two, phase degree, simple connectedness, a global square-root branch, the disk
  inverse, or Boyd--Nemes equation `(15)`.

## Prior state and attack angle

- `assumption_frontier_before`: Loop 20 publicly proves that `Phi : D -> B` is proper. Loops
  17--19 classify all finite critical points, construct both adjacent phase contours, and prove
  their exact normalized-coordinate radial lifts.
- `hard_gap_before`: properness excludes compact-target escape but does not say that `D` is one
  component or that `Phi` covers `B`. The phase zero fiber has not been classified in the first
  strip, so the number of source components cannot yet be controlled.
- `known_obstacles`: `phase` has a double critical zero at the origin, so ordinary unbranched
  covering theorems do not apply there. Direct star-shapedness is not evident and radial phase
  monotonicity fails on the full strip. The proof must transport openness and closedness through
  both source and target subtypes and turn an `ENat` connected-component bound into an actual
  connected-space statement.
- `nearest_primary_source`: Boyd 1995 Conditions 2.1 and its Gamma adjacent-saddle domain;
  Boyd 1994, DOI `10.1098/rspa.1994.0158`; Nemes arXiv `1310.0166`, equation `(15)`.
- `nearest_project_attempt`: Loop 20
  `K0-H6-BOYD-STRIP-PHASE-PROPERNESS-01` and residual
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `new_attack_angle`: avoid a direct path construction in `D`. First classify the zero fiber by
  elementary real and imaginary equations. The complex open mapping theorem makes `Phi` open,
  while properness makes it closed. Mathlib's theorem
  `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton` then bounds the number of
  source components by the cardinality of the zero fiber. A singleton fiber forces one component;
  the same open/closed pair then makes the range all of the connected target disk.

## Audited proof skeleton

1. Expand `phase(u)=0` into
   `exp(x)*cos(y)=x+1` and `exp(x)*sin(y)=y`.
2. By conjugation reduce to `0<=y<2*pi`. If `pi<=y`, the imaginary equation contradicts the
   nonpositivity of `sin(y)`. If `0<y<pi`, positivity of `sin(y)` and the real equation force
   `y<pi/2`; use `Real.lt_tan` to derive `x<0`, then `Real.sin_lt` and `exp(x)<1` contradict the
   imaginary equation. Hence `y=0`.
3. With `y=0`, the real equation is `exp(x)=x+1`; strict convexity in
   `Real.add_one_lt_exp` forces `x=0`. Transfer the nonnegative-imaginary proof to negative
   imaginary part by complex conjugation.
4. Apply the global complex open mapping theorem to the entire phase. Exclude the constant branch
   using its values at `0` and `1`, then restrict to the open source subtype and codomain subtype.
5. Give the target disk its connected-space instance from convexity and positive radius. Rewrite
   the fiber of target zero as the singleton containing source zero.
6. Use Loop 20 properness to obtain a closed map. Apply the connected-component cardinal theorem,
   the finite singleton fiber, and the resulting cardinal bound to make the source component type
   subsingleton. Convert this to `PreconnectedSpace D`; source zero supplies nonemptiness and hence
   connectedness.
7. The range of `Phi` is open and closed, and it contains target zero. Connectedness of `B` forces
   the range to be all of `B`, yielding surjectivity.

## Runtime and gate

- `compaction_state`: Loop 21 began from an inherited summary after Loop 20 closure. The canonical
  governance, HANDOFF, Targets/TargetChecks, current attempt, hard-gap DAG, Loop 20
  preregistration and production source, and the relevant mathlib open-map, proper-map, connected-
  component-cardinality, and subtype-connectedness APIs were re-read before this preregistration.
- `downloads_patch_check`: `/Users/karasuakamatsu/Downloads/RH_GOVERNANCE_V4_PATCH.zip` has SHA-256
  `95820ea9624685c1e272889b159a49e98adc67844219bbaf3083b77b5e59550d`, exactly matching the
  existing adapted import record. V4.1 remains authoritative over superseded V4 gates.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no V4.1 numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
- `previous_public_ledger`: Loop 20 final ledger commit
  `8fae21e1af69095ab2c7fefa3763957e61505365` passed public Lean Action CI run `29669353109`,
  build job `88145481490`, in `1m46s`.

No Loop 21 Lean proof source may be edited before this preregistration passes public Lean Action
CI.
