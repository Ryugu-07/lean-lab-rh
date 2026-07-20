# H6 Boyd Branched Degree-Two Loop 22 Preregistration

Date: 2026-07-20

Campaign: `PROOF-ATTEMPT-20260720-H6-BOYD-BRANCHED-DEGREE-TWO-01`

Mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED / AWAITING_PUBLIC_CI`

## Target

- `node_id`: residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `relation_to_RH`: this is the degree-computation layer required before the proper Boyd phase map
  can be lifted through its normalized square-root coordinate to the disk-wide inverse used in the
  `R_2` representation feeding the Polymath final-region certificate.

Retain the publicly compiled Loop 20--21 definitions and facts

```text
phase(u) = exp(u) - u - 1,
D = {u : C | |im(u)| < 2*pi and norm(phase(u)) < 2*pi},
B = {z : C | norm(z) < 2*pi},
Phi : D -> B.
```

Loop 22 removes the unique branch value `0`. Prove that `Phi` is a covering map over
`B \ {0}`. Compute the fiber over the positive real target `1` exactly: first use the imaginary
phase equation to prove that every preimage of a positive real phase in the first strip is real;
then use the Loop 16 global real saddle-coordinate order isomorphism and
`phase(u)=coordinate(u)^2/2` to identify the two preimages with the inverse-coordinate values at
`-sqrt(2)` and `sqrt(2)`. Prove that the punctured disk is path connected and use covering
monodromy to transport this two-point fiber to every nonzero target in `B`.

Together with the compiled singleton zero fiber, the double analytic zero at the origin, and the
compiled absence of other critical points over `B`, this is the exact branched degree-two
certificate. It is not yet a proof that the normalized coordinate is globally injective or that
Boyd--Nemes equation `(15)` holds.

## Proposed Lean declarations

Exact helper names and the representation of punctured subtypes may vary while preserving the
three final statements.

```lean
theorem isCoveringMapOn_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_away_zero :
    IsCoveringMapOn deBruijnNewmanPolymathBoydPhaseOnOriginDomain
      {deBruijnNewmanPolymathBoydOpenPhaseDiskZero}ᶜ

theorem deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_one :
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
        {deBruijnNewmanPolymathBoydOpenPhaseDiskOne} =
      {deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage,
        deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage}

theorem natCard_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_eq_two_of_ne_zero
    (z : deBruijnNewmanPolymathBoydOpenPhaseDisk)
    (hz : z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero) :
    Nat.card (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z}) = 2
```

The pseudocode uses ASCII where convenient. Production statements will use exact Lean syntax and
may expose a named covering map between the punctured source and target subtypes as an additional
aggregate theorem.

## Success and falsification

- `success_criterion`: the actual subtype phase map is a covering on the punctured target disk;
  the target-one fiber is exactly the two compiled real inverse-coordinate points and those points
  are distinct; the punctured target disk is path connected; and every nonzero target fiber has
  kernel-checked cardinality two by covering monodromy. Exact Targets/TargetChecks, selected
  standard-only axiom prints, forbidden scans, full build, and public implementation/evidence CI
  must pass.
- `falsification_criterion`: a nonreal preimage in `D` of the positive real phase `1`; a third
  preimage of `1`; failure of local invertibility at a nonzero source point; a disconnected
  punctured target disk; or a nonzero target fiber not equivalent to the target-one fiber.
- `proper_prefix_rule`: if the global cardinality transport is blocked by a missing monodromy or
  subtype-fiber interface, retain the covering theorem only if it applies to the actual `Phi`, all
  regular fibers are proved finite, every point over the punctured disk is given an actual local
  open partial homeomorphism, and the first missing transport statement is recorded precisely.
  Derivative nonvanishing alone, an ambient phase theorem detached from `D -> B`, or only an
  upper bound on one fiber does not qualify.
- `anti_substitution_rule`: do not infer degree two from the origin double zero alone; do not
  assume fiber-cardinality constancy, target path connectedness, a global square-root branch,
  normalized-coordinate injectivity, the disk inverse, adjacent-saddle decomposition, or
  Boyd--Nemes equation `(15)`.

## Prior state and attack angle

- `assumption_frontier_before`: Loop 20 proves `Phi` proper. Loop 21 proves `D` connected, `Phi`
  open and surjective, and its zero fiber singleton. Loop 17 proves that the phase derivative is
  nonzero at every nonzero point over `B`. Loop 15 proves the origin is an analytic double zero;
  Loop 16 gives the global real normalized-coordinate order isomorphism.
- `hard_gap_before`: a double zero in one ramified fiber does not determine the number of points in
  a regular fiber. A genuine covering over the regular-value locus and one exact regular-fiber
  computation are still required.
- `known_obstacles`: the inverse-function theorem must be transported through both open subtypes;
  proper compact fibers must be combined with local discreteness to obtain finiteness; the
  punctured disk path-connectedness certificate must preserve the disk radius; and monodromy
  fibers of the restricted covering must be related exactly to the original singleton-preimage
  subtypes.
- `nearest_primary_source`: Boyd 1995 Conditions 2.1 and its Gamma adjacent-saddle domain; Boyd
  1994, DOI `10.1098/rspa.1994.0158`; Nemes arXiv `1310.0166`, equation `(15)`.
- `nearest_project_attempt`: Loop 21
  `K0-H6-BOYD-PHASE-DOMAIN-CONNECTEDNESS-01` and residual
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `new_attack_angle`: compute one regular fiber from the already compiled global real saddle
  coordinate instead of trying to localize all small fibers by a new compactness argument. The
  imaginary phase equation excludes nonreal preimages of a positive real target. Mathlib's
  `IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph` then supplies the regular covering, while
  `IsCoveringMap.monodromy_bijective` transports the exact two-point baseline fiber throughout the
  punctured disk.

## Audited proof skeleton

1. For a point `u in D` with nonzero target value, use the Loop 17 derivative theorem and the
   analytic inverse-function theorem to build an ambient local open partial homeomorphism. Restrict
   its source to `D` and codomain to `B`, obtaining a local open partial homeomorphism whose total
   function is exactly `Phi`.
2. For each nonzero `z in B`, properness makes `Phi⁻¹({z})` compact. The local homeomorphisms make
   that fiber discrete, so compactness makes it finite. Apply the closed-map covering criterion to
   obtain `IsCoveringMapOn Phi ({0}ᶜ)` and its punctured-subtype covering map.
3. Define target `1 in B`. If `phase(x+i*y)=r` for real `r>0`, use
   `exp(x)*sin(y)=y`. For `y>0`, exclude `y>=pi`; then `sin(y)<y` forces `x>0`.
   If `y>=pi/2`, the real phase is negative. If `0<y<pi/2`, `y<tan(y)` gives
   `exp(x)*cos(y)<1`, again making the real phase negative. Conjugation handles `y<0`.
4. Every target-one preimage is therefore real. The Loop 16 identity turns its real coordinate
   into a solution of `w^2=2`, hence `w=+/-sqrt(2)`. The global real inverse supplies both points,
   and order-isomorphism injectivity proves they are distinct. Rewrite the full target-one fiber as
   exactly this pair.
5. Construct a homeomorphism from `C` to `B` using mathlib's open-ball homeomorphism, verify that it
   maps zero to target zero, and restrict it to complements. Transport the standard path
   connectedness of `C \ {0}` to the punctured target subtype.
6. For arbitrary nonzero `z`, choose a path in the punctured target subtype from target one to `z`.
   Covering monodromy along that path is bijective on fibers. Compose with the exact subtype-fiber
   equivalences and the target-one pair computation to prove `Nat.card(Phi⁻¹({z}))=2`.
7. Package the singleton zero fiber, sole critical point, and two-point regular fibers as the
   precise branched degree-two ledger result, without claiming the normalized-coordinate lift.

## Runtime and gate

- `compaction_state`: Loop 22 began from an inherited summary after Loop 21 public closure. The
  canonical governance, HANDOFF, Targets/TargetChecks, current attempt, hard-gap DAG, Loop 21
  preregistration and production source, and the relevant mathlib covering, local inverse,
  monodromy, open-ball-homeomorphism, compact-discrete-finiteness, and path-connectedness APIs were
  re-read before this preregistration.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no V4.1 numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
- `previous_public_ledger`: Loop 21 final ledger commit
  `f9ccc509b1e857cd23eb0bacaa796da7481523ec` passed public Lean Action CI run `29670505425`,
  build job `88148483185`, in `1m37s`.

No Loop 22 Lean proof source may be edited before this preregistration passes public Lean Action
CI.
