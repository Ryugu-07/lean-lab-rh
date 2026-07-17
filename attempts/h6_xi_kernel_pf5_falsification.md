# H6 Actual Xi-Kernel PF5 Falsification

Campaign: `FALSIFICATION-20260717-H6-XI-KERNEL-PF5-01`

Mode: `FALSIFICATION`

Status: `PUBLICLY_CLOSED`

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

## Lean implementation record

- Module: `LeanLab/Riemann/XiKernelPF5Falsification.lean`.
- `pf5ExpTaylor_sub_error_le_exp` and `pf5Exp_le_taylor_add_error` specialize Mathlib's
  `Real.exp_bound` to rational lower and upper certificates; no decimal or external interval is a
  proof premise.
- `pf5_first_three_term_bounds` encloses the first three exact theta summands at all nine witness
  arguments. `pf5_phi_tail_term_le_geometric` and `pf5_phi_tail_tsum_lt` prove the complete
  omitted infinite tail is below `10^-12` at each argument.
- `pf5_phi_bounds` therefore encloses each full `deBruijnNewmanPhi` `tsum`; the center error is
  strictly below `3*10^-12` entrywise.
- Lean checks an explicit rational LU factorization of the center matrix and proves
  `xiKernelPF5CenterMatrix_det_lt`, with bound `det(C) < -9/5000000000`.
- A five-factor telescoping lemma and the full 120-term Leibniz formula prove
  `xiKernelPF5_det_center_error`, bounding the determinant perturbation by `1/5000000000`.
- `xiKernelPF5ToeplitzMatrix_det_neg` proves the exact full-series source matrix has negative
  determinant. The ordered witnesses `x_i=1/200+i/20` and `y_j=-1/200+j/20` then prove
  `not_isPolyaFrequencyFive_deBruijnNewmanEvenKernel` for the source-faithful quantified PF5
  predicate.

## Local audit

- Standalone module compilation is diagnostic-free.
- Exact Targets and TargetChecks build and resolve the endpoint name and statement witnesses.
- AxiomsAudit reports only `propext`, `Classical.choice`, and `Quot.sound` for the full-kernel
  enclosure, center determinant, exact determinant, and PF5-negation endpoint.
- The forbidden placeholder/declaration/resource scan is empty, `git diff --check` passes, and the
  root `lake build` passes all 8,699 jobs.
- Classification: `ACTUAL_KERNEL_PF5_FORMALLY_FALSIFIED`.
- `hard_gap_delta=0`, `route_infrastructure_delta=1`, `obstruction_map_delta=1`.
- Scope: this refutes PF5, hence PF-infinity, for the physical Xi kernel. It does not decide global
  PF4, H6-E/G8, or RH.

## Public evidence

- Implementation commit: `7bdf2b9ab08f2b298d1565921158ff9a199c867a`.
- Public Lean Action CI run: `29565362144`.
- Build job: `87836632525`, success in `2m39s`.
- The local campaign is closed. The persistent RH Goal remains active and returns to value-ranked
  route selection.
