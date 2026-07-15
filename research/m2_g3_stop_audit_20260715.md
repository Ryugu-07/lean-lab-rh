# M2/G3 Automatic-Loop Stop Audit

Date: 2026-07-15

Audit ID: `AUDIT-20260715-M2-G3-03`

## Fixed-Gap Entry

- `node_id`: `M2`
- `gap_id`: `G3`
- `work_class`: `AUDIT/LITERATURE`
- `novelty_label`: `NOVELTY_UNCHECKED` for rejected candidates; no result admitted.
- `status`: complete
- `hard_gap_before`: M2/G3 parked; M0, M1, D, and G4 complete.
- `assumption_frontier_before`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`.
- `expected_hard_gap_delta`: zero unless a remaining 2025-2026 source contains an unconditional
  estimate not equivalent to the fixed closure target.
- `batch_reason`: this is the mandatory independent stop audit after two consecutive admitted
  M2/G3 audits retained the same assumption frontier.

## Sources Screened

### Iyer 2026 residual dynamics

Rajah Iyer, *Residual Dynamics for Summation-Integral Approximation and a Nyman-Beurling
Stability Interface for the Riemann Zeta Function* (June 2026).

The abstract and Sections 9-10 explicitly state that the paper does not prove RH. Corollary 9.3
assumes every nontrivial zero is residual-covariant; Problem 9.4 asks for a proof of that premise.
The conclusion identifies the required weighted Hilbert residual/boundary-control theorem with
the known RH-equivalent Nyman-Beurling approximation problem. It therefore preserves, rather than
reduces, the fixed assumption frontier.

### Alvarez Cruz-Alvarez Gutierrez 2026 Colombeau criterion

Amaury Alvarez Cruz and Esteban A. Alvarez Gutierrez, *A Colombeau-Beurling criterion for the
Riemann hypothesis*, arXiv `2606.22562v2`.

The abstract states a two-way equivalence. Moderateness, uniform `L2` boundedness, and association
of the damped net are proved assuming RH; conversely those properties imply RH. This is a new
criterion carrier, not an unconditional approximant.

### Bhattacharjee-Nandi-Frederick-Samal 2026 spectral structure

*Spectral and Analytic Structure of the Nyman-Beurling-Baez-Duarte Approximation*,
Preprints.org `202506.0772v2`.

The paper explicitly says it does not prove RH. Its advertised rank-one collapse uses
`r_k(x)={x/k}` on `(0,1)`, whereas the exact published positive-natural carrier already aligned in
this project is `rho(1/(k*x))` in `L2(0,infinity)`. Its later sawtooth replacement `{k*x}` is a
different computational family. No theorem in the source proves unconditional membership of the
actual target in the actual kernel closure.

### Dyadic computational exploration

The June 2026 public description labels itself a conditional reduction with finite-tail
computational evidence and a remaining block-decay bottleneck. Numerical tail suppression is
excluded by the fixed G3 rule and Burnol rate boundary as evidence of closure membership.

## Admission Decision

No candidate supplies all of:

1. an unconditional theorem;
2. the exact M0/M1-aligned NB/BD carrier;
3. a strict reduction of the unproved closure-membership frontier;
4. a source-valid bridge from auxiliary smoothing, residual dynamics, or computation to that
   closure statement.

Accordingly no Lean statement is preregistered and no mathematical source file is edited.

## Result

- `result`: `NO_PROGRESS`
- `audit_decision`: `STOP`
- `hard_gap_after`: M2/G3 remains parked; M0, M1, D, and G4 remain complete.
- `hard_gap_delta`: zero.
- `assumption_frontier_after`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`.
- `Lean_verification`: not applicable; no mathematical proposition was admitted.
- `theorem_names_added`: none.
- `repository_verification`: `git diff --check` and the unchanged 8617-job project build pass.

## Stop Rule

The following three consecutive M2/G3 loops have `hard_gap_delta=0` and retain the same unproved
assumption frontier:

1. `AUDIT-20260715-M2-G3-01`: Wong projection branch, `BRANCH_FALSIFIED`;
2. `AUDIT-20260715-M2-G3-02`: Carvill ladder-frequency branch, `BRANCH_FALSIFIED`;
3. `AUDIT-20260715-M2-G3-03`: remaining-candidate audit, `NO_PROGRESS`.

Loop Protocol v2 therefore requires automatic looping to stop. M2/G3 may be reconsidered only
after a new external source or an independently proposed structural estimate is accompanied by a
specific unconditional statement, closest-results comparison, and a credible bridge to the fixed
closure frontier. Repackaging an equivalent criterion, auxiliary smoothing, or numerical evidence
is insufficient.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no
