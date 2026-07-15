# M2/G3 Ladder-Frequency Branch Audit Pre-Registration

Date: 2026-07-15

Audit ID: `AUDIT-20260715-M2-G3-02`

## Fixed-Gap Entry

- `node_id`: `M2`
- `gap_id`: `G3`
- `work_class`: `AUDIT/LITERATURE`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete
- `hard_gap_before`: M2/G3 parked; M0, M1, D, and G4 complete.
- `assumption_frontier_before`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`.
- `expected_hard_gap_delta`: zero unless the audited unconditional structural estimate survives
  source-level verification and supplies a valid bridge to the unsmoothed closure frontier.
- `batch_reason`: the exact frequency-to-lattice-distance conversion is the decisive theorem
  boundary for the candidate's claimed arbitrary-order Gram decay and block compressibility.

## Candidate Source

Hugh Carvill, *Beurling-Nyman Geometry and Gram Matrix Structure: Ladder Density and Polynomial
Decay via Mellin Smoothing*, arXiv `2510.18132` (2025). Inspected PDF SHA-256:
`c72c144f3d088032895be0903267757e1618065f034b70d814453cd8b758635f`.

The source studies the ladder `theta_(j,k)=2^(-j)3^(-k)`. In the proof of Theorem 6.1 on PDF
page 8 it defines

```text
lambda = (j'-j) log 2 + (k'-k) log 3,
d = |j-j'| + |k-k'|,
c = min(log 2, log 3),
```

and asserts `|lambda| >= c*d`. This step converts an oscillatory estimate in `|lambda|` into the
claimed polynomial decay in ladder distance.

## Exact Lean Audit Endpoint

Use the source's admissible distinct ladder indices

```text
(j,k)=(0,2),    (j',k')=(3,0).
```

For this pair, `d=5` and `lambda=3*log(2)-2*log(3)`. Lean must verify the strict reverse inequality

```text
|3*log(2)-2*log(3)| < min(log(2),log(3))*5.
```

The proof must use exact monotonicity and logarithm identities, not floating-point evaluation.
Package the endpoint both as the strict inequality and as the negation of the source's lower bound.

## Admission And Scope

- This audit is admitted because the source advertises an unconditional structural estimate that,
  if correct and connected to the original carrier, could motivate a novelty-audited M2 edge.
- Falsifying the displayed lower bound rejects this proof route only. It does not by itself prove
  that every possible Gram-decay statement is false and does not change RH.
- No successor M2 node may be created from smoothing, compressibility, or finite sections unless
  the frequency geometry and the bridge back to the unsmoothed closure are independently valid.
- No `sorry`, `admit`, project `axiom`, unchecked `constant`, `opaque` premise, `native_decide`, or
  resource-limit relaxation is permitted.

## Closest Literature Boundary

- Baez-Duarte's positive-natural criterion remains an exact RH equivalence, not an unconditional
  approximant.
- Burnol and later distance work constrain approximation rates conditionally and do not provide
  this ladder-frequency lower bound.
- Yang's 2026 Friedrichs-angle paper gives a different subspace-geometric result; its advertised
  RH-facing angle conclusion is RH-conditional, while its unconditional theorem does not assert
  target closure membership.

## Result Rules

- `BRANCH_FALSIFIED`: the strict reverse inequality and negated source bound compile.
- `DEPENDENCY_GAP_IDENTIFIED`: the exact comparison cannot be completed, but the missing
  frequency-separation premise is isolated without assuming it.
- `NO_PROGRESS`: only unrelated logarithm facts compile.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no

## Audit Result

Lean checks the source-facing endpoint in `LeanLab/Riemann/M2LadderFrequencyAudit.lean`:

```text
m2AuditCarvillLadderDistance 0 2 3 0 = 5,
m2AuditCarvillLadderFrequency 0 2 3 0 = 3*log(2)-2*log(3),
not (min(log(2),log(3))*5 <= |3*log(2)-2*log(3)|).
```

The proof uses exact logarithm monotonicity with `2^3<3^2<2^4`; it uses no floating-point
evaluation. Hence the frequency lower bound invoked on PDF page 8 fails for the source's own
admissible ladder indices.

- `result`: `BRANCH_FALSIFIED`
- `hard_gap_after`: M2/G3 remains parked; M0, M1, D, and G4 remain complete.
- `hard_gap_delta`: zero.
- `assumption_frontier_after`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`.
- `governance_decision`: reject the current polynomial-distance-decay proof route; do not create
  an M2 successor from smoothed Gram compressibility.
- `local_verification`: exact target checks, standard-only axiom audit, empty forbidden scans,
  `git diff --check`, and the 8617-job full build pass.
- `public_verification`: implementation commit
  `ff0f14f10e75d73424addb671b3da34f0c44c679` passed Lean Action CI run `29384172003`, build job
  `87253877106`, in 2m34s.

The result falsifies a decisive proof step, not necessarily every alternative form of Gram decay.
Any repair must control Diophantine cancellation in the actual logarithmic frequency and must
separately prove that estimates for the smoothed ladder imply progress for the original NB/BD
target closure. Neither requirement may be assumed.
