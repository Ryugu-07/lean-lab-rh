# H6 Boyd Strip Properness Loop 20 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-STRIP-PROPERNESS-01`

Mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED`

## Target

- `node_id`: residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `relation_to_RH`: two-dimensional no-asymptotic-singularity layer required before the Boyd
  normalized saddle coordinate can be continued across its first critical-value disk and used in
  the `R_2` representation feeding the Polymath final-region certificate.

Let

```text
phase(u) = exp(u) - u - 1,
S = {u : C | |im(u)| < 2*pi},
D = {u : C | |im(u)| < 2*pi and norm(phase(u)) < 2*pi},
B = {z : C | norm(z) < 2*pi}.
```

The phase induces a continuous map `Phi : D -> B`. Prove that `Phi` is proper. The concrete
compactness engine is the closed-strip phase sublevel

```text
K(r) = {u : C | |im(u)| <= 2*pi and norm(phase(u)) <= r}.
```

For every `0 <= r < 2*pi`, prove `K(r)` is compact and lies in the open strip `S`. Then prove that
the inverse image under `Phi` of every compact subset of `B` is compact. This is the exact
topological statement that an inverse path whose phase remains in a compact subdisk cannot escape
to infinity or collide with either strip boundary.

This campaign does not assume or claim that `D` is connected or simply connected, that the phase
has topological degree two on `D`, that the normalized coordinate is analytic or injective on all
of `D`, or that the disk-wide inverse already exists.

## Proposed Lean declarations

Exact helper names may vary while preserving the final proper-map statement.

```lean
def deBruijnNewmanPolymathBoydOriginPhaseStrip : Set C :=
  {u | |u.im| < 2 * Real.pi}

def deBruijnNewmanPolymathBoydOriginPhaseDomain : Set C :=
  {u | |u.im| < 2 * Real.pi and
    norm (deBruijnNewmanPolymathBoydComplexSaddlePhase u) < 2 * Real.pi}

def deBruijnNewmanPolymathBoydOpenPhaseDisk : Set C :=
  Metric.ball 0 (2 * Real.pi)

def deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    deBruijnNewmanPolymathBoydOriginPhaseDomain ->
      deBruijnNewmanPolymathBoydOpenPhaseDisk

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_norm_ge_two_pi_of_abs_im_eq
    {u : C} (hu : |u.im| = 2 * Real.pi) :
    2 * Real.pi <= norm (deBruijnNewmanPolymathBoydComplexSaddlePhase u)

theorem isCompact_deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel
    {r : R} (hr : 0 <= r) :
    IsCompact {u : C | |u.im| <= 2 * Real.pi and
      norm (deBruijnNewmanPolymathBoydComplexSaddlePhase u) <= r}

theorem deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel_subset_originStrip
    {r : R} (hr : r < 2 * Real.pi) :
    {u : C | |u.im| <= 2 * Real.pi and
      norm (deBruijnNewmanPolymathBoydComplexSaddlePhase u) <= r} <=
      deBruijnNewmanPolymathBoydOriginPhaseStrip

theorem isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    IsProperMap deBruijnNewmanPolymathBoydPhaseOnOriginDomain
```

The pseudocode uses ASCII type names and relations only for portability. Production statements
will use exact Lean syntax.

## Success and falsification

- `success_criterion`: the boundary lower bound, compactness of every nonnegative closed-strip
  phase sublevel, strict-strip inclusion for `r < 2*pi`, and the actual subtype-valued
  `IsProperMap` theorem compile. Exact Targets/TargetChecks, selected standard-only axiom prints,
  forbidden scans, full build, and public implementation/evidence CI must pass.
- `falsification_criterion`: a point on `|im u|=2*pi` has phase norm below `2*pi`; a bounded phase
  sequence in the closed strip escapes in real part; or a compact subset of the open target disk
  has noncompact inverse image in `D`.
- `proper_prefix_rule`: if the subtype proper-map packaging is blocked, retain results only if the
  compact sublevel theorem, strict-boundary exclusion, and an exact compact-preimage theorem for
  arbitrary compact target subsets all compile. Real-part bounds alone do not qualify.
- `anti_substitution_rule`: do not assume compactness, properness, connectedness, simple
  connectedness, phase degree, a global square-root branch, global injectivity, the disk inverse,
  absence of critical points, or Boyd--Nemes equation `(15)`.

## Prior state and attack angle

- `assumption_frontier_before`: Loop 17 classifies every finite phase critical point and isolates
  the first critical-value radius. Loop 18 constructs both adjacent phase contours and Loop 19
  proves their exact normalized-coordinate radial lifts. All are public K0.
- `hard_gap_before`: the two boundary lifts do not exclude an interior inverse path with bounded
  phase value escaping to infinity. No compact-preimage or proper-map theorem exists for the
  two-dimensional source domain.
- `known_obstacles`: `phase` is not globally proper on `C`; it has unbounded families of remote
  inverse behavior, so the horizontal strip restriction is essential. Compact subsets of an open
  disk require extraction of a strict radius margin before the closed-sublevel theorem applies.
  The domain and codomain are subtypes, so the final proof must transport compactness through
  subtype embeddings without replacing the requested proper-map statement by prose.
- `nearest_primary_source`: Boyd 1995 Conditions 2.1 and the Gamma adjacent-saddle discussion at
  `https://intlpress.com/site/pub/files/_fulltext/journals/maa/1995/0002/0004/MAA-1995-0002-0004-a007.pdf`;
  Boyd 1994, DOI `10.1098/rspa.1994.0158`; Nemes arXiv `1310.0166`, equation `(15)`.
- `nearest_project_attempt`: Loops 17--19, especially
  `K0-H6-BOYD-COORDINATE-RAYS-01` and residual
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01`.
- `new_attack_angle`: use the exact strip geometry rather than either distinguished boundary ray.
  On `|im u|=2*pi`, the imaginary part of `phase(u)` has magnitude `2*pi`. For `re u <= 0`, a
  bounded phase gives a direct lower real-part bound. For `re u >= 0`, the triangle inequality and
  a quadratic lower bound for `exp(re u)` give an explicit upper real-part bound. Heine--Borel
  then yields compact phase sublevels, and compactness of arbitrary target inverse images gives
  the proper map.

## Audited proof skeleton

1. Expand real and imaginary parts of `phase(x+i*y)`. At `|y|=2*pi`, use
   `sin(+/-2*pi)=0` to get `|im(phase(u))|=2*pi`, hence `2*pi <= norm(phase(u))`.
2. Prove the closed sublevel is closed by continuity of `u -> |im u|` and
   `u -> norm(phase(u))`.
3. If `x=re u <= 0`, use `exp(x)<=1` and `cos(y)>=-1` to derive an explicit lower bound for `x`
   from `norm(phase(u))<=r`.
4. If `0<=x`, use `exp(x)=norm(exp(u))<=r+norm(u+1)`, the strip bound on `y`, and a certified
   quadratic lower estimate for `exp(x)` to derive an explicit upper bound for `x`.
5. Combine the real and imaginary bounds to prove boundedness and then compactness of `K(r)`.
6. For `r<2*pi`, the boundary theorem rules out equality `|im u|=2*pi`, so `K(r) subset S`.
7. Let `L` be compact in the target-disk subtype. If nonempty, maximize the ambient norm on `L`
   to obtain `r<2*pi`. Express the ambient image of `Phi preimage L` as a closed subset of `K(r)`;
   transport compactness back through the domain subtype embedding. Handle `L=empty` separately.
8. Apply `isProperMap_iff_isCompact_preimage` to package the final `IsProperMap` theorem.

## Runtime and gate

- `compaction_state`: Loop 20 began from an inherited summary after Loop 19 closure. Current
  governance, HANDOFF, Targets, the current attempt, hard-gap DAG, Loops 17--19 records, production
  phase/coordinate sources, and relevant mathlib compactness/proper-map APIs were re-read before
  this preregistration.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no V4.1 numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
- `previous_public_ledger`: Loop 19 final ledger commit
  `420a009f0f1350beb0f6dbdc8c9aa38d3c2a71d7` passed public Lean Action CI run `29668411637`,
  build job `88142934757`, in `2m0s`.

No Loop 20 Lean proof source may be edited before this preregistration passes public Lean Action
CI.

