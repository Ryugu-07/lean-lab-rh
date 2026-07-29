# H1 Hardy--Littlewood Linear Count Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01`

Node: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_PENDING`

## Parent and selection

- `parent_closure`: Hardy tangential-theta receipt
  `af2dece69203d9f9fa83cee9dc896d5a6ec8fe76`, Lean Action run `30436760730`,
  build job `90526205899`, passed in `2m44s`.
- `selected_node`: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`.
- `selection_reason`: the earliest quantitative theorem after Hardy's now-compiled qualitative
  infinitude is the 1921 linear lower bound. Its decisive exceptional-set and interval-pair
  inference is absent, while later Selberg and Levinson--Conrey routes all need compatible
  finite-height count production.
- `material_difference`: this campaign does not continue Hardy's theta limit, optimize a
  constant, or rebuild the already compiled local strict-gap theorem. It reconstructs the
  source's global measure-to-distinct-count transition.

## Source lock

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), Theorem A, equations `(2.81)`--`(2.87)`,
  and section `2.9`:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

The fixed source logic is:

```text
I(t,H)    = integral_[t,t+H] X(u) du
absI(t,H) = integral_[t,t+H] |X(u)| du

absI(t,H) >= A*H - |psi(t)|
integral_[T,2T] |psi(t)|^2 dt <= B*T
integral_[T,2T] |I(t,H)|^2 dt <= C*H*T

outside U = {|psi| > A*H/2} and V = {|I| >= A*H/2}:
|I(t,H)| < absI(t,H).
```

The strict gap forces a zero in `(t,t+H)`. Pairing disjoint adjacent `H`-intervals then turns a
measure bound for `S=U union V` into many distinct zeros.

## Fixed definitions

Create `LeanLab/Riemann/HardyLittlewoodLinearCount.lean` only after preregistration public CI.
Names may be adjusted to established local style, but the mathematical statements may not be
weakened silently.

1. Define the real window integral and absolute window integral.
2. Define the two source-shaped bad-start sets and their union.
3. Define the first and paired intervals for a finite family indexed by `Fin n`.
4. Define a zero-coordinate adapter requiring continuity and exact equivalence between coordinate
   zeros and actual nontrivial critical-line zeta zeros. Do not identify `hardyXi` with the
   source Hardy `X` normalization.

## Fixed Lean endpoint

`FULL_SUCCESS` requires all of the following.

1. Prove measurability and interval integrability needed for the window objects from explicit
   continuity or integrability hypotheses.
2. Prove the two exact Chebyshev/Markov bounds:
   the measure of `{t in [T,2T] | A*H/2 < |psi t|}` is bounded by
   `4*B*T/(A^2*H^2)`, and the measure of
   `{t in [T,2T] | A*H/2 <= |I(t,H)|}` is bounded by
   `4*C*T/(A^2*H)`, in an equivalent denominator-free form if this is cleaner in `ENNReal`.
3. Prove that outside their union, the source lower inequality implies the strict triangle gap
   `|I(t,H)| < absI(t,H)`.
4. For `n` disjoint adjacent interval pairs, prove that every failed pair charges one entire
   first interval of measure `H` to the exceptional set.
5. Derive a natural-number lower bound for the number of good pairs from the exceptional-set
   measure. The theorem must preserve interval endpoints and cannot replace measure by a count
   of sampled grid points.
6. For every continuous real coordinate with exact actual-zero equivalence, select one zero
   from each good pair and prove the selected ordinates are injective.
7. Package a corollary with a fixed positive fraction of the `n` pairs good whenever the
   exceptional-set measure is less than the corresponding fraction of `n*H`. This is the finite
   exact form of the source's linear-count conclusion.
8. Compile the negative control: the finite set of all left endpoints has measure zero while
   containing every sampled endpoint, so endpoint sampling cannot replace the interval-subset
   argument.
9. Combine the analytic bad-set bounds, pair count, actual-zero witnesses, and negative control
   in one endpoint certificate.

Register one proven Target and exact TargetChecks. Add selected standard-only axiom prints to
`AxiomsAudit.lean`. Import the module from `LeanLab.lean`.

## Success, partial, and obstruction criteria

`FULL_SUCCESS` requires all nine fixed items, no placeholders, warning-as-error compiles, exact
TargetChecks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, a full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires:

- both exact L2-to-measure bounds;
- the union strict-gap theorem;
- the finite adjacent-pair cardinality theorem;
- an exact statement of the first unavailable actual-zero adapter or injective-selection step.

`SOURCE_LOGIC_FALSIFIED` requires a compiled counterexample to the literal finite
exceptional-set-to-pair-count implication with all preregistered endpoint and measurability
conditions satisfied.

`BLOCKED_API` is not mathematical failure. It requires the exact missing Mathlib theorem for
finite disjoint interval measure, `ENNReal` arithmetic, or finite subtype selection, while
retaining every compiled source subtheorem.

## Negative controls

- A small-measure set may contain every finitely sampled left endpoint. Endpoint sampling is not
  a substitute for finding one point outside the exceptional set in an entire first interval.
- A zero in two overlapping windows must not be counted twice. Only disjoint paired blocks may
  support the injectivity proof.
- Equality `|I|=absI` is compatible with a constant-sign nonzero window. The proof requires a
  strict gap.
- A real continuous coordinate with the same zeros as zeta is sufficient for the count consumer,
  but its moment estimates do not automatically transfer from Hardy `Z` under arbitrary positive
  rescaling.
- An abstract finite model or `hardyXi` moment package is not the source's unconditional
  Hardy--Littlewood theorem.

## Obstacle map

- `OBS-H1-HARDY-LITTLEWOOD-ETA-LOWER-01`: formalize the actual Dirichlet-eta integral lower
  estimate and its error second moment in the source normalization.
- `OBS-H1-HARDY-LITTLEWOOD-X-MEAN-SQUARE-01`: formalize source Lemma 11 for the actual real
  Hardy `X`/`Z` coordinate.
- `OBS-H1-HARDY-Z-NORMALIZATION-01`: construct the source real critical-line coordinate with
  continuity, exact zeta-zero equivalence, and normalization compatible with the moment
  estimates.
- `OBS-H1-SELBERG-GLOBAL-MOMENT-01`: produce the later `T log T` family of mollified strict-gap
  intervals.
- `OBS-H1-SPARSE-EXCEPTION-01`: a linear or positive-proportion theorem does not exclude a
  finite or density-zero off-line orbit.

The campaign may close only the exceptional-set/count bridge. The persistent RH Goal remains
active after every local outcome.

## Audit gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. exact checks for every registered theorem;
4. selected `#print axioms` output contains only accepted standard foundations;
5. warning-as-error compile of the new module and registration files;
6. full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop this local campaign and rerank all
historical routes.

## Local implementation result

The frozen endpoint is implemented in
`LeanLab/Riemann/HardyLittlewoodLinearCount.lean`.

The compiled chain is:

```text
continuous X
-> continuous moving integrals I(t,H) and absI(t,H)
-> strict/non-strict square Markov inequalities
-> the two source-shaped bad-set bounds
-> a denominator-free bound for their union
-> strict local triangle gap outside the union
-> a whole length-H first-block charge for every failed pair
-> a natural lower bound n-b for good pairs
-> injective actual critical-line zeta-zero ordinates
```

`hardyLittlewood_source_finite_count` combines the two moment hypotheses, the source lower
estimate, the exact `[T,2T]` restricted-measure block calculation, the cardinality argument, and
the actual-zero adapter in one theorem. `hardyLittlewood_positiveHalf_corollary` packages a fixed
positive-fraction finite consequence. `hardyLittlewoodEndpointSet_volume_zero` compiles the
endpoint-sampling negative control.

The final theorem requires the lower estimate only on `[T,2T]`; its generic zero consumer requires
it only inside the finitely many first blocks. An earlier local draft used an unnecessary global
quantifier, which was removed before freeze so that the producer premise matches the source.

The implementation is 867 lines, compiles with `-DwarningAsError=true`, has exact TargetChecks,
and the selected axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The three forbidden scans and `git diff --check` are empty, and the full build passes
`8798/8798` with inherited replay warnings only.

The following source producers remain open exactly as preregistered:

- the actual Hardy `X`/`Z` normalization and exact zero adapter;
- the Dirichlet-eta lower estimate and its error second moment;
- the actual source-coordinate moving-integral second moment;
- the asymptotic choice of `H`, `n`, and `b` that discharges the finite budget uniformly.

Consequently this is the full finite measure-to-count inference from Hardy--Littlewood 1921,
not the paper's unconditional asymptotic linear-count theorem, a positive-proportion theorem,
H1, or RH.

Frozen implementation commit `8f3742c62a381293fa201358cf58130d2c333c48` passed public Lean
Action run `30464674314`, build job `90619318156`, in `2m52s`. The five proof and registration
files are now frozen; the next gate is docs-only immutable evidence.

Immutable-evidence commit `9f161104ed086a137e221b6c8ffe3d3bdda65005` passed public Lean
Action run `30465073931`, build job `90620648692`, in `2m14s`. The frozen five-file diff remains
empty. The next gate is the docs-only final ledger.

Final-ledger commit `25316ea1b408731da6581a371afcaccd2bf169f7` passed public Lean Action
run `30465345680`, build job `90621575136`, in `1m41s`. Publish one docs-only closure receipt;
after its public CI succeeds, close only this fixed finite count bridge.
