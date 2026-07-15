# R1 q=2 Baez-Duarte Criterion Campaign

Campaign: `CAMPAIGN-20260715-R1-BAEZ-DUARTE-QTWO-01`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget; campaign capped by Discovery Protocol V3
- `compaction_since_previous_campaign`: yes

## Loop 1: Route Map

- Audited the closed R5 finite-height zero-cutoff frontier against Lagarias's source class.
- Deferred the height limit because bounded closed-strip transforms do not supply vertical decay.
- Rechecked the R1 sparse lower-frame and exact orthogonal-obstruction campaigns.
- Preserved the exclusion of the `(2^24)^j` target-coupling branch.

## Loop 2: Candidate Generation

- Generated five normalized candidates covering exact natural Gram evaluation, modified
  Levinson-Selberg coefficients, the q=2 criterion, generic projection residuals, and alternate
  sparse subsequences.
- Exact tuples and source positions are recorded in
  `research/r1_baez_duarte_qtwo_prereg_20260715.md`.

## Loop 3: Adversarial Test

- Rejected exact Gram formulas without asymptotic residual control.
- Rejected the modified-coefficient route because its decisive estimates are explicitly open.
- Rejected generic finite projection algebra and sparse-family constant changes.
- Admitted only the q=2 convolution criterion.
- No numerical result or unproved candidate has been admitted as a premise.

## Fixed Endpoint

```lean
RiemannHypothesis <->
  baezDuarteQTwoComplexTargetL2 in baezDuarteQTwoComplexKernelClosure
```

The implementation must replace ASCII `in` by `∈`, prove the exact Mellin and tail identities, and
establish both implications. Partial carrier helpers do not close the campaign.

## Frontier Before Proof

- `hard_gap_before`: unconditional q=1 closure membership remains open
- `hard_gap_after`: unchanged during route selection
- `hard_gap_delta`: zero
- `assumption_frontier_before`: no unconditional exact target-closure membership
- `assumption_frontier_after`: unchanged
- `activity_result`: `ROUTE_SELECTION_COMPLETE`
- `research_progress`: none yet

## Next Loop

`PROOF_ATTEMPT_A`: construct the exact q=2 convolution carrier in `L2(0,infinity)`, compile its
Mellin values and reciprocal tail, and continue in the same engineering batch to the two directions
of the fixed criterion. No `sorry`, project axiom, `native_decide`, or relaxed resource option is
admissible.

## Loop 4: Proof Attempt A

- Added `LeanLab/Riemann/BaezDuarteQTwo.lean` with the exact convolution carriers
  `chi *_M chi` and `chi *_M rho_n` in complex `L2(0,infinity)`.
- Proved the exact Mellin identities `1 / s^2` and
  `n^(-s) * (-zeta(s) / s^2)`, plus the target formula and the reciprocal kernel tail.
- Constructed the critical-line multiplier by `1 / s` as a continuous linear map of norm at
  most `2`, then transported it through the project's Fourier-Mellin isometry.
- Proved, in Lean, that the transported operator sends the `q = 1` target and every natural
  generator exactly to their `q = 2` counterparts.
- Lifted the generator identity through finite span and closure, obtaining
  `RiemannHypothesis.baezDuarteQTwoComplexTargetL2_mem_kernelClosure`.
- The module compiles with no errors, `sorry`, project axiom, `native_decide`, or relaxed resource
  option. Remaining linter warnings are local proof-style warnings to remove before audit.

## Frontier After Attempt A

- `forward_direction`: complete
- `reverse_direction`: open
- `fixed_endpoint`: open
- `hard_gap_before`: unconditional q=1 closure membership remains open
- `hard_gap_after`: unchanged
- `hard_gap_delta`: zero
- `activity_result`: `PROOF_ATTEMPT_A_FORWARD_COMPLETE`
- `research_progress`: exact q=2 criterion forward half formalized

## Next Loop After Attempt A

`PROOF_ATTEMPT_B`: prove independently that q=2 target closure excludes every zeta zero with
real part greater than `1/2`, using the q=2 Mellin value, the shared reciprocal tail, and local
Cauchy-Schwarz control. Then invoke the functional-equation symmetry already formalized in the
project to recover the full Riemann hypothesis. The bounded forward multiplier is not invertible
and must not be used as a reverse implication.

## Loop 5: Proof Attempt B

- Defined complex finite `q = 2` kernel sums and their exact reciprocal tail moment.
- Proved every finite sum has Mellin value zero at a zeta zero in the critical strip.
- Proved the full `L2(0,infinity)` approximation norm controls both the unit-interval error and
  the norm of the reciprocal tail moment.
- Combined local Cauchy-Schwarz with the target Mellin value `1 / s^2` to exclude every zeta zero
  with `1/2 < re(s) < 1` from q=2 target-closure membership.
- Used the already-audited functional-equation reflection to obtain
  `baezDuarteQTwoComplexTarget_mem_closure_imp_riemannHypothesis`.
- Closed the exact fixed endpoint as
  `riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure`.
- The reverse implication is independent of the bounded forward multiplier and never assumes an
  inverse multiplier.
- `BaezDuarteQTwo.lean` compiles with no warnings. `TargetChecks.lean` compiles, and all eight new
  selected declarations in `AxiomsAudit.lean` report only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Frontier After Attempt B

- `forward_direction`: complete
- `reverse_direction`: complete
- `fixed_endpoint`: complete
- `hard_gap_before`: unconditional q=1 closure membership remains open
- `hard_gap_after`: unconditional q=2 closure membership remains equivalent to RH and open
- `hard_gap_delta`: zero
- `assumption_frontier_before`: exact q=2 equivalence not formalized
- `assumption_frontier_after`: exact q=2 equivalence formalized with standard axioms only
- `activity_result`: `FIXED_ENDPOINT_COMPILED`
- `research_progress`: exact published q=2 RH criterion formalized; no unconditional RH progress

## Next Loop After Attempt B

`INDEPENDENT_AUDIT`: run forbidden-token and custom-axiom scans, exact TargetChecks, selected axiom
prints, `git diff --check`, and the full project build. Record the campaign as an exact criterion
formalization only if every gate passes. The persistent RH Goal remains active after campaign
closure.

## Loop 6: Independent Audit

- Rechecked the source-facing target as `chi *_M chi` and every generator as `chi *_M rho_n`.
- Rechecked the exact transforms `1/s^2` and `n^(-s) * (-zeta(s)/s^2)` and the `x>1`
  reciprocal tail.
- Adversarially verified that the forward proof uses a bounded multiplier only in the forward
  direction and that the reverse proof reconstructs the zero obstruction independently.
- Standalone Lean compilation and the 8,608-job module build pass; the new 1,604-line module has
  no warnings.
- Exact `TargetChecks.lean` passes. Eight selected q=2 declarations in `AxiomsAudit.lean` depend
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder, explicit declaration, `native_decide`, unsafe/opaque declaration, and
  resource-relaxation scans are empty.
- `git diff --check` passes.
- The full project build passes all 8,668 jobs. Replayed warnings are confined to pre-existing
  modules.

## Local Closure

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `fixed_endpoint`: complete
- `hard_gap_delta`: zero
- `unconditional_RH_progress`: none
- `assumption_frontier_delta`: exact q=2 criterion is now available without new assumptions
- `next_state`: publish implementation, verify public CI, backfill immutable evidence, then return
  to `INDEPENDENT_AUDIT -> ROUTE_SELECTION`
- The persistent RH Goal remains active.

## Public Implementation Evidence

- implementation commit: `90313d83210bdfe0aca8b62153240d51e0c924b1`
- public repository: `Ryugu-07/lean-lab-rh`, branch `main`
- Lean Action CI run: `29430307834`
- build job: `87403316754`
- conclusion: success in `2m20s`
- immutable evidence-backfill commit and its CI remain to be recorded.
