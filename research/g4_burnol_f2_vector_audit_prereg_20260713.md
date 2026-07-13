# G4-F2 Burnol Vector Audit Pre-Registration

Date: 2026-07-13

Batch ID: `AUDIT-20260713-G4-F2-01`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F2`
- `work_class`: `LITERATURE_AND_DEPENDENCY_AUDIT`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

This audit must recover the exact construction and orthogonality theorem for Burnol's vectors
`Y(lambda,s,k)`. It may not identify the completed F1b distance isometry with Burnol's second
phase operator, nor replace the source vectors by arbitrary members of an orthogonal complement.

## Audit Questions

1. Which unitary is denoted `V` in the source, and how is it related to the Mellin transform of
   the explicit F1a function `A`?
2. What is the exact physical cutoff `Q_lambda`, and why does it preserve the transformed model
   generators for `lambda <= theta`?
3. Which left-half-plane vectors `psi(w,k)` approach the critical line, and what exact filter and
   `L2` limit define `Y(lambda,s,k)`?
4. Which source theorem proves existence of that boundary limit, and which estimates must be
   retained so F3 can later prove Gram asymptotics?
5. How does the source inner-product convention translate to Mathlib's complex inner product and
   to the project's unnormalized kernels `A(t/theta)`?
6. Which analytic-order statement is sufficient to put `Y(lambda,rho,k)` in the orthogonal
   complement of the explicit model span?

## Anti-Shortcut Gate

- A vector defined by choosing an arbitrary element of `burnolModelKernelSpan lambda`'s
  orthogonal complement does not satisfy F2.
- A `lim` or `Classical.choose` definition without a proved source boundary convergence theorem
  and physical representative estimates does not satisfy F2.
- The phase operator, cutoff projector, or pre-boundary pairing alone is partial infrastructure.
- F2 may close only when existence, the exact boundary pairing, lambda-independent representative
  estimates needed by F3, and zero-order orthogonality compile together.

## Result Rules

- `DEPENDENCY_GAP_IDENTIFIED`: the exact source unitary, cutoff, oscillatory continuation theorem,
  available Lean APIs, missing APIs, and one indivisible implementation boundary are fixed.
- `BRANCH_FALSIFIED`: the source construction is incompatible with the completed F1 normalization.
- `FORMALIZATION_ONLY`: only generic phase or projector wrappers are obtained.
- `NO_PROGRESS`: no source-facing implementation boundary is recovered.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no

## Result

- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `hard_gap_after`: G4/F2 remains open and selected with one indivisible implementation batch;
  F3-F5 and M2/G3 are unchanged.
- `hard_gap_delta`: no theorem edge is closed; the hidden second phase operator and oscillatory
  boundary-continuation dependency are now fixed.
- `assumption_frontier_after`: the source burden is separated into an internal Gate A
  (`V`, `Q_lambda`, `psi`, pre-boundary pairing) and Gate B (oscillatory continuation, exact `L2`
  limit, representative estimates, boundary pairing, and zero-order orthogonality). Both gates are
  required in the same F2 completion batch.
- `commit_SHA`: `6aa73266bf0697383f535358160a033e0fcd2893`
- `public_CI`: Lean Action run `29232724946` succeeded; build job `86760317208`
