# H7 Connes Nested-Projection Positive-Type Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H7-CONNES-PROJECTION-DEFECT-01`

Node: `H7-CONNES-NESTED-PROJECTION-POSITIVE-TYPE-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

## Parent and selection

- `parent_closure`: H1 Levinson--Siegel step closure receipt
  `00b731ca0686c44e899acfacea6bb51e18b8cfbb`, public Lean Action run
  `30410732753`, build job `90445972599`, passed in `1m31s`.
- `selected_node`: `H7-CONNES-NESTED-PROJECTION-POSITIVE-TYPE-01`.
- `selection_reason`: Connes' original absorption-spectrum trace route remains unreconstructed
  as a distinct project mechanism. Its first exact positivity step is finite algebra once the
  source containment of cutoff subspaces is available.
- `material_difference`: this is neither the Berry--Keating half-line mode nor the 2025--2026
  finite-prime Weil ground-state route. It audits Connes 1998 Theorem 5 equations `(23)`--`(25)`.

## Source lock

Primary source:

Alain Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
function*, arXiv `math/9811068`, Theorem 5, especially equations `(23)`--`(25)`:
<https://arxiv.org/abs/math/9811068>.

The source obtains an orthogonal-projection containment

```text
Q'_Lambda <= S_Lambda
```

and defines

```text
D_Lambda(f) = Trace((S_Lambda-Q'_Lambda) V(f)).
```

For convolution squares, the representation law turns `V(f*f*)` into `A*A*`, and the source
deduces positive type. This campaign formalizes that algebraic inference and its nesting
boundary. It does not formalize the actual global-field Hilbert space.

## Fixed definitions

After preregistration public CI, create
`LeanLab/Riemann/ConnesProjectionDefect.lean`.

For a finite index type and complex square matrices `P`, `Q`, and `A`, define a predicate for
nested orthogonal projections containing exactly:

```text
Pᴴ = P
P * P = P
Qᴴ = Q
Q * Q = Q
P * Q = Q
Q * P = Q
```

Define the defect `H=P-Q` and the finite trace distribution on a convolution-square image by

```text
Trace(H * (A * Aᴴ)).
```

Names may follow local conventions, but no hypothesis may be dropped or strengthened silently.

## Fixed Lean endpoint

`FULL_SUCCESS` requires all of the following.

1. Prove `Hᴴ=H` and `H*H=H`.
2. Prove the exact complex trace identity

   ```text
   Trace(H * (A * Aᴴ))
     = coe(sum_i sum_j normSq((H*A) i j)).
   ```

3. Derive that the trace has imaginary part zero and nonnegative real part.
4. Prove that the trace vanishes exactly when `H*A=0`.
5. Package the result as the finite positive-type core of
   `Trace((S-Q') V(f*f*)) >= 0`.
6. Give a compiled `1 x 1` negative control: `P=0`, `Q=1`, and `A=1` are individual
   orthogonal projections but the defect trace has real part `-1`, because nesting is absent.
7. Combine the positive mechanism and the negative control in one endpoint theorem.

Register one proven Target and exact TargetChecks. Add selected standard-only axiom prints to
`AxiomsAudit.lean`. Import the module from `LeanLab.lean`.

## Success, partial, and failure criteria

`FULL_SUCCESS` requires all seven fixed items, no placeholders, warning-as-error compiles,
exact TargetChecks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the exact trace-as-square identity and real nonnegativity under
all six nested-projection hypotheses, even if the zero characterization or aggregate negative
control remains uncompiled.

`FALSIFIED_SOURCE_INFERENCE` requires a compiled counterexample satisfying all six exact
nested-projection hypotheses but having negative trace real part.

`BLOCKED_API` is not mathematical failure. It requires recording the exact missing
conjugate-transpose, trace-cyclicity, or finite-sum interface and retaining every compiled
subtheorem.

## Negative controls and claim boundary

- Individual self-adjoint idempotence of `P` and `Q` does not imply positivity of `P-Q`.
- The product of two positive operators need not itself be self-adjoint; the proof must use
  trace cyclicity and the idempotence of the defect.
- A finite matrix theorem is not an infinite trace-class theorem.
- No actual `Q_Lambda`, `S_Lambda`, adèle class space, representation `V`, or distributional
  limit may be asserted from the abstract matrix result.
- No Weil positivity, Hilbert--Polya operator, H7, or RH may be inferred.

## Obstacle map

- `OBS-H7-CONNES-ADELE-PROJECTIONS-01`: construct the source number-field Hilbert space and
  actual nested cutoff projections.
- `OBS-H7-CONNES-TRACE-CLASS-01`: prove the relevant cutoff products are trace class with the
  source normalization.
- `OBS-H7-CONNES-DISTRIBUTION-LIMIT-01`: identify the uniform cutoff limit with the full Weil
  distribution, including all finite and archimedean places.
- `OBS-H7-CONNES-POSITIVITY-TO-RH-01`: connect the complete positive-type distribution to the
  already compiled exact Weil criterion without losing the test class.

The campaign may close only the finite positive-type inference. The persistent RH Goal remains
active after every local outcome.

## Preregistration and local outcome

- `preregistration_commit`: `59a6d8aa74fb48c3123e391e50e2e932408bcf66`.
- `preregistration_public_ci`: Lean Action run `30411132179`, build job `90447227409`,
  passed in `1m33s`.
- `classification`: `FULL_SUCCESS / SOURCE_POSITIVE_TYPE_HINGE_FORMALIZED`.
- `production_module`: `LeanLab/Riemann/ConnesProjectionDefect.lean`.
- `proven_target`: `H7.connes.nested-projection-defect-positive-type`.
- `positive_result`: the six exact nesting hypotheses make `P-Q` a self-adjoint idempotent,
  and the defect trace is exactly the sum of the squared norms of the entries of `(P-Q)A`.
- `boundary_result`: `P=0`, `Q=1`, and `A=1` in dimension one satisfy the individual
  projection laws but have defect-trace real part `-1`; nesting is therefore essential.
- `audit`: 192-line production module, eight exact TargetChecks, seven selected axiom prints
  containing only `propext`, `Classical.choice`, and `Quot.sound`, empty forbidden/resource
  scans, warning-as-error compiles, `git diff --check`, and full build `8793/8793`.
- `deltas`: historical route coverage `+1`, source-logic map `+1`, hard gap `0`, RH frontier
  `0`.
- `next_gate`: freeze the implementation and require independent public CI before publishing
  immutable evidence.

The frozen implementation commit `25c18e31cd882f9ad2f43fe26900e450d98c0500` passed public Lean
Action run `30411787173`, build job `90449324931`, in `2m1s`. The five frozen proof and
registration files have an empty diff from that commit. The next gate is docs-only immutable
evidence and its independent public CI.

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
