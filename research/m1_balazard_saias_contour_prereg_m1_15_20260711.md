# M1 Balazard-Saias Contour Completion Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-15`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/F1/Balazard-Saias/contour-shifting-and-error-balancing`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

The sole target is the source-equivalent RH specialization already accepted in the M1-10
pre-registration: without assuming `BalazardSaiasEstimate`, prove that for every `delta>0` and
`eta>0` there is a constant `C>0`, uniform in `N>=2` and
`1/2+delta<=Re(s)<=1`, such that

```text
norm(mobiusDirichletPartialSum N s - analyticReciprocalRiemannZeta s)
  <= C * N^(-delta/3) * (1+|Im(s)|)^eta.
```

Here `analyticReciprocalRiemannZeta` is the holomorphic reciprocal through the pole of zeta and
has value zero at `s=1`. Mathlib's raw `riemannZeta 1` is a finite regularized point value, so its
field inverse is not the source function at the endpoint. This discrepancy was found and corrected
during the batch.

The general zero-free-half-plane proposition `BalazardSaiasEstimate` remains a separate stronger
source statement. This batch may close the RH-to-Burnol forward block F1 if the sole target
compiles, but it must not claim that the general `alpha` theorem has then been formalized.

## Sources And Exact Route

The quantitative target is Burnol, Theorem 1.4, citing Balazard-Saias, Lemma 2. The contour shape
is reconstructed from Titchmarsh, Theorem 14.25(A), after the already compiled Titchmarsh 14.2
reciprocal-zeta bound and Lemma 3.12 truncated Perron formula. Inspected local sources:

- `/tmp/burnol-analytic-estimate.pdf`;
- `/tmp/TitchmarshZeta.pdf`, SHA-256
  `ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`.

For `0<delta<=1/2`, put `x=N+1/2`, `H=1+|Im(s)|`, `T=x^3*H`, and shift from `Re(w)=2` to

```text
Re(w) = 1/2 + delta/3 - Re(s).
```

Thus the shifted reciprocal-zeta argument has real part `1/2+delta/3`, while the Perron factor
contributes at most `x^(-2*delta/3)`. Use a reciprocal-zeta height exponent
`q=min(delta/12,eta/2)`. The three source errors then have the schematic powers

```text
truncation:  x^2/T,
left edge:   x^(-2*delta/3) * T^q,
horizontal: x^2 * T^(q-1).
```

The logarithmic vertical-edge integral must be proved, not replaced by a length-times-supremum
bound. Compact and right-half-plane portions of the horizontal edges must be controlled by a
checked extension of the existing RH reciprocal-zeta subpower argument. The case `delta>1/2` is
vacuous under the target strip inequalities.

## Existing Checked Inputs

- `RiemannHypothesis.exists_reciprocalZeta_subpower_bound`;
- `exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le`;
- the entire pole removal `zetaPoleRemoved` and rectangle Cauchy-Goursat API;
- the exact Burnol consumer and its `eta<1/8` integrable majorant.

None of these inputs asserts the target estimate.

## Classification Rules

- `HARD_GAP_REDUCED`: the sole target compiles without an unchecked premise and replaces `hBS`
  in the fixed Burnol forward consumer. Remove only the RH-specialized Balazard-Saias/F1 edge.
- `KNOWN_THEOREM_FORMALIZED`: the target compiles but is not yet connected to the fixed consumer.
- `DEPENDENCY_GAP_IDENTIFIED`: the target remains open, but the contour proof isolates a strictly
  smaller source-level analytic dependency not already present in the DAG.
- `FORMALIZATION_ONLY`: only generic contour or inequality infrastructure compiles.
- `NO_PROGRESS`: the fixed frontier and its exact dependency boundary are unchanged.

## Assumption And Gap Frontier Before

- `hard_gap_before`: truncated Perron and RH reciprocal-zeta subpower are closed; the entire
  contour shift and quantitative balance remain inside `G2/F1/Balazard-Saias`.
- `assumption_frontier_before`: every Burnol theorem still receives `hBS : BalazardSaiasEstimate`.
- `hard_gap_after`: the RH-specialized Balazard-Saias forward estimate and its Burnol consumer are
  compiled; the general-alpha source proposition, reverse base criterion, G1, D, and RH remain open.
- `hard_gap_delta`: remove `G2/F1/Balazard-Saias/contour-shifting-and-error-balancing` and the
  explicit `hBS` edge from the fixed RH-to-Burnol forward consumer.
- `assumption_frontier_after`: `exists_norm_burnolMobiusTransformedError_le_compiled` depends on RH
  but has no `BalazardSaiasEstimate` premise.
- `result_class`: `HARD_GAP_REDUCED`.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; the continuation summary was checked against the clean
  worktree, current target ledger, hard-gap DAG, relevant Lean modules, and pinned source files.
- `verification`: full `lake build` passes with 8604 jobs; incomplete-proof and explicit-declaration
  scans have no matches; target checks, axiom audit, and `git diff --check` pass. The two compiled
  main theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Public commit `25f4117`
  passes Lean Action CI run `29151912852`, job `86542626185`.
