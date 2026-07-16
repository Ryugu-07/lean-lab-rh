# G4-F2 Burnol Vector Audit

Date: 2026-07-13

- `batch_id`: `AUDIT-20260713-G4-F2-01`
- `node_id`: `B1`
- `gap_id`: `G4/F2`
- `work_class`: `LITERATURE_AND_DEPENDENCY_AUDIT`
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `hard_gap_before`: F2 selected; F3-F5 open; M2/G3 historically unselected (open under V4.1).
- `hard_gap_after`: F2 remains selected with one exact indivisible implementation boundary;
  F3-F5 and M2/G3 unchanged.
- `hard_gap_delta`: no theorem edge closed; corrected the source dependency boundary.

## Findings

- The completed F1b unitary `T=(1-M)^(-1)` is not Burnol's F2 phase `V`. The latter is the phase
  of the Mellin transform of `A` and has source multiplier
  `(s/(1-s))^3*zeta(1-s)/zeta(s)` almost everywhere.
- `V` must be totalized at critical-line zeros; those ordinates form an already compiled null set.
- The generic phase, cutoff `Q_lambda`, and left-half-plane vectors `psi(w,k)` only recover the
  pre-boundary pairing. They do not prove the existence of `Y`.
- Existence depends essentially on the oscillatory kernels `phi(w,k)`. The `k=0` estimates invoke
  BBLS Lemmas 4 and 6; Burnol proves the `k>=1` integral and series extension.
- F3 needs lambda-independent physical representative bounds, so an arbitrary Riesz or
  orthogonal-complement construction with the same generator pairings is not an acceptable `Y`.
- The source inner product is linear in the first argument; Burnol's `(D_theta A,Y)` translates to
  Mathlib's `inner Y (D_theta A)`.
- The project's `A(t/theta)` differs from normalized `D_theta A` by the positive scalar
  `sqrt(theta)`; orthogonality is unaffected, but the exact pairing must record it.

## Decision

Keep F2 as one indivisible completion batch with internal Gates A and B. Gate A packages the true
phase, cutoff, dilation, time reversal, `psi`, and pre-boundary pairing. Gate B formalizes the
oscillatory continuation, boundary `L2` limit, F3-ready estimates, boundary pairing, and
analytic-order orthogonality. Gate A alone is at most `FORMALIZATION_ONLY`.

Detailed source matrix: `research/g4_burnol_f2_vector_audit_20260713.md`.
Fixed implementation target: `research/g4_burnol_f2_prereg_20260713.md`.

## Audit

- Source SHA-256: `8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.
- No Lean theorem was added in this literature loop.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed).
- `reasoning_effort`: not exposed.
- `budget`: unbounded persistent-goal budget.
- `compaction_state`: no compaction during this audit.
- `commit_SHA`: `6aa73266bf0697383f535358160a033e0fcd2893`.
- `public_CI`: Lean Action run `29232724946` succeeded; build job `86760317208`.
