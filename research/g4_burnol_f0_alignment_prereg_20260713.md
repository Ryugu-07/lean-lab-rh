# G4-F0 Burnol Continuous/Natural Alignment Pre-Registration

Date: 2026-07-13

Batch ID: `BATCH-20260713-G4-F0`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F0`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

This engineering batch implements the full F0 edge identified by the source audit. It must be one
batch, not separate loops for definitions, span inclusion, distance monotonicity, or filter
transport.

## Exact Lean Surface

The batch will add one module with:

```text
burnolContinuousParameter
burnolContinuousKernelL2
burnolKernelSet
burnolKernelSpan
burnolDistance
baezDuarteFiniteComplexKernelSet
baezDuarteFiniteComplexKernelSpan
baezDuarteNaturalDistance
burnolContinuousParameterOfNatural
burnolContinuousKernelL2_ofNatural
baezDuarteFiniteComplexKernelSpan_le_burnolKernelSpan
burnolDistance_inv_natCast_le_baezDuarteNaturalDistance
tendsto_natCast_inv_nhdsWithin_Ioi_zero
```

The central statements are, for `0 < N`,

```text
baezDuarteFiniteComplexKernelSpan N <=
  burnolKernelSpan ((N : Real)^-1)
```

and

```text
burnolDistance ((N : Real)^-1) <= baezDuarteNaturalDistance N.
```

## Source And Frontier

Burnol, arXiv `math/0103058v2`, defines `B_lambda` using all real parameters
`lambda <= theta <= 1`. The project's finite natural kernels use `theta=1/n`; for `n<=N`, reciprocal
order gives `1/N<=1/n`. Distance reverses this inclusion.

- `hard_gap_before`: F0 is source-audited but no continuous space or distance exists in Lean.
- `assumption_frontier_before`: no mathematical assumption; the gap is exact representation.
- `expected_hard_gap_delta`: close F0 only. G4/F1-F5, M2, G3, and RH are unchanged.
- `reason_batched`: all objects and lemmas express one source inclusion and are mechanical without
  the group.

## Classification Rules

- `FORMALIZATION_ONLY`: the complete F0 surface compiles and exact inclusion/distance direction is
  witnessed in `TargetChecks.lean`.
- `BRANCH_FALSIFIED`: Lean reveals that the source/project inclusion or distance direction in the
  literature audit is wrong.
- `NO_PROGRESS`: only definitions compile without the central inclusion and distance inequality.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; automatic compaction occurred immediately before the
  implementation resumed from the retained handoff summary.

## Result

- `result_class`: `FORMALIZATION_ONLY`
- `hard_gap_after`: F0 is closed; G4/F1-F5 remain open, and F1 is the next source-level edge.
- `hard_gap_delta`: representation/alignment edge F0 closed; no RH hard gap and no M2/G3 node changed.
- `assumption_frontier_after`: no mathematical assumption was added. The transfer uses only
  `V_N <= B_(1/N)`, monotonicity of `infDist`, and `1/N -> 0+`.
- `Lean_verification`: all preregistered names compile and the three central statements have exact
  witnesses in `LeanLab/Riemann/TargetChecks.lean`.
- `axiom_audit`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `commit_SHA`: `1383db8e9cea271874b7f4f399eb35d1cf07f103`
- `public_CI`: success, run `29225515844`, build job `86738660740`.
