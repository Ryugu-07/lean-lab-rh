# H6 Actual Xi-Kernel PF5 Falsification

Campaign: `FALSIFICATION-20260717-H6-XI-KERNEL-PF5-01`

Mode: `FALSIFICATION`

Status: `PREREGISTRATION_PENDING_PUBLIC_CI`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited continuation; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, H6 route card, the closed TP2 attempt, and the new primary source
  were reread before selection
- `global_goal`: active

## Selection record

- `exact_target`: prove the actual full-series `5x5` Toeplitz determinant at
  `(u0,h)=(1/100,1/20)` is negative and derive a source-faithful `not PF5` witness
- `primary_source`: Michałowski 2026, arXiv:2602.20313, unreviewed preprint
- `external_code_pin`: `675058772f2ba4bf409d114b6082ac9990b78b34`
- `material_difference`: certify a substantive analytic property of the actual kernel rather than
  a vacuous external Lean predicate or a finite truncation
- `nearest_attempt`: closed actual Xi-kernel TP2 campaign
- `assumption_frontier_before`: actual `Phi`, positivity, two derivative series, strict TP2, and
  strong Gaussian tail tools compile; no PF-order definition, rational exp enclosure layer, or
  nontrivial physical-kernel determinant sign is compiled
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open

## Reproduction and pre-proof audit

- exact source TeX was fetched from arXiv and the public code repository was pinned
- `verify_pf5.py` was reproduced with `mpmath==1.3.0`; at the exact target it reports
  determinant midpoint approximately `-1.847236073e-9` and a strictly negative interval
- the script's floating interval chain is not a Lean premise
- the nine kernel arguments after absolute value lie in `[1/100,21/100]`
- the determinant sign has enough margin that entry enclosures of roughly `1e-11` should suffice
  via a coarse five-dimensional Leibniz perturbation bound
- Mathlib provides `Real.exp_bound` with an arbitrary Taylor order on `abs x<=1`, so rational
  exponential enclosures can in principle be proved without an oracle
- the principal risk is proof-term and arithmetic size when nesting rational bounds for
  `exp(-pi*n^2*exp(4u))`, not the finite determinant algebra

## Frozen success rule

Only the exact full-`tsum` negative determinant plus the ordered `not PF5` witness counts as
success. External interval output, decimal evaluation, an abstract determinant lemma, or a finite
kernel prefix is insufficient. On failure, record the first exact enclosure or arithmetic
normalization that Lean cannot close and return the persistent Goal to route selection.
