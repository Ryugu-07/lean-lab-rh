# G4-F2 Burnol Boundary Vectors Pre-Registration

Date: 2026-07-13

Batch ID: `BATCH-20260713-G4-F2`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F2`
- `work_class`: `SOURCE_FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: preregistered

Formalize Burnol's `Y(lambda,s,k)` boundary vectors, their source physical estimates, exact model-
kernel pairings, and zero-order orthogonality as one indivisible batch. F2 may not close after only
constructing a phase multiplier, cutoff projection, left-half-plane vectors, or generic limit API.

## Parameter Domain

```text
0 < lambda <= 1,
re(s) = 1/2,
k : Nat,
re(w) < 1/2 for the approximating vectors.
```

The boundary filter is `nhdsWithin s {w | re(w)<1/2}`. The cutoff is physical multiplication by
the indicator of `[lambda,infinity)`, with endpoint differences treated only by null-set equality.

## Required Lean Surface

The batch must expose source-facing declarations covering at least:

```text
burnolZ
burnolAPhaseMultiplier
burnolAPhaseL2
burnolTimeReverseL2
burnolNormalizedModelKernelL2
burnolCutoffL2
burnolPsi
burnolPsiL2
burnolPreY
burnolPhi
burnolYTransformed
burnolY
tendsto_burnolPreY
inner_burnolY_normalizedModelKernel
burnolY_mem_modelKernelSpan_orthogonal
```

Names may change to follow local conventions, but the final exact target checks must witness all
four theorem surfaces: source boundary convergence, physical representative estimates, exact
pairing, and full-span orthogonality under the analytic-order condition.

## Exact Source Identities

On the critical line, the total phase must agree almost everywhere with

```text
conj(Z(s))/Z(s)
  = (s/(1-s))^3 * zeta(1-s)/zeta(s).
```

At zeros it must remain total and unit modulus without dividing by zero. The operator must satisfy
`V(A)=J(A)` and commute with normalized multiplicative dilation.

For `re(w)<1/2`, define

```text
PreY(lambda,w,k) = V^(-1) Q_lambda V(psi(w,k)).
```

For every critical-line `s`, prove a named `Y(lambda,s,k)` and

```text
Tendsto (fun w => PreY(lambda,w,k))
  (nhdsWithin s {w | re(w)<1/2})
  (nhds (Y(lambda,s,k))).
```

For `lambda<=theta<=1`, expose the normalized source pairing

```text
inner (Y lambda s k) (D_theta A)
  = (-d/ds)^k [theta^(s-1/2) * Z(s)],
```

using Mathlib's inner-product convention. Also expose the exact positive scalar relation between
`D_theta A` and the existing unnormalized `burnolModelKernelL2 theta`.

## F3 Readiness Gate

The transformed representative of `Y` must be explicit and satisfy bounds with constants
independent of `lambda`:

```text
V(Y)(t) = 0                                      for 0<t<lambda,
norm(V(Y)(t) - d^k/ds^k[V(s)t^(-s)]) <= C       for lambda<t<=1,
norm(V(Y)(t)) <= C*(1+abs(log t))^2/t            for 1<=t.
```

Equivalent a.e. formulations and harmless endpoint changes are permitted. A mere existence
theorem with no representative bounds does not close F2 because F3 consumes these estimates.

## Orthogonality Gate

For critical-line `s`, prove at least the forward source implication

```text
zeta(s)=0 ->
(k+1 : ENat) <= analyticOrderAt riemannZeta s ->
Y(lambda,s,k) in (burnolModelKernelSpan lambda)^orthogonal.
```

The proof must pass through the exact pairing and derivative vanishing. Defining `Y` from the
orthogonal complement, or assuming derivative vanishing as an unchecked premise, is forbidden.

## Implementation Route

1. Construct the total frequency phase from `Z` and package the `L2` isometry with conjugate
   inverse; prove source quotient agreement almost everywhere.
2. Construct time reversal, normalized dilation, cutoff, and `psi(w,k)`, then prove the exact
   pre-boundary pairing.
3. Formalize the oscillatory kernel `phi(w,k)`: import no unchecked theorem. Prove the `k=0`
   BBLS estimates and Burnol's `k>=1` integral/series formula in Lean.
4. Apply the two Hardy averages, establish one lambda-independent square-integrable majorant, and
   use dominated convergence for the physical cutoff limit.
5. Transport through the inverse phase to define `Y`, retain the physical representative bounds,
   and pass the pairing to the boundary.
6. Use analytic order and span induction to prove orthogonality for every model generator.

## Batch Gates

- Gate A infrastructure does not close F2 by itself.
- Gate B may not use a proposition, typeclass, or local axiom encoding the oscillatory estimates.
- No `sorry`, `admit`, project axiom, opaque unchecked premise, or source theorem postulated as a
  variable is permitted.
- F3 remains forbidden until the exact target checks and axiom audit for all F2 surfaces pass.

## Frontier

- `hard_gap_before`: G4/F2 open and selected; F3-F5 open; M2/G3 parked and unchanged.
- `assumption_frontier_before`: the source `V`, oscillatory continuation, boundary convergence,
  physical estimates, pairing, and order orthogonality are external facts.
- `expected_hard_gap_delta`: close F2 only and select F3 next.
- `hard_gap_after_on_success`: F2 complete; F3 selected; F4-F5 and M2/G3 unchanged.

## Result Rules

- `KNOWN_THEOREM_FORMALIZED`: every required surface, including F3-ready bounds, compiles and
  passes exact target, axiom, local, and public CI checks.
- `DEPENDENCY_GAP_IDENTIFIED`: a narrower source theorem is exposed, with F2 still open and no
  unchecked premise inserted.
- `BRANCH_FALSIFIED`: the source phase, cutoff, limit, pairing, or normalization is inconsistent.
- `NO_PROGRESS`: only generic phase/projector infrastructure compiles.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no
