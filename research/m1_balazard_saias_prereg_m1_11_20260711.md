# M1 Balazard-Saias Source-Proof Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-11`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/F1/Balazard-Saias`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

The fixed gap remains the Balazard-Saias quantitative Mobius partial-sum estimate. This batch may
only work on a source-proof dependency of that estimate; it may not replace the estimate by an
absolute-convergence result in `Re(s) > 1` or by a project-local wrapper.

## Source-Proof Audit

The authoritative comparison proof is E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory
of the Riemann Zeta-function*, second edition, Sections 3.12, 14.2, and 14.25. The inspected scan is
`/tmp/TitchmarshZeta.pdf`, SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`.

The proof decomposes into:

1. a truncated Perron formula for Dirichlet partial sums (Lemma 3.12);
2. a subpower bound for `1 / zeta(s)` in a zero-free half-plane, obtained by applying
   Borel-Caratheodory and Hadamard interpolation to an analytic branch of `log zeta`
   (Theorem 14.2, especially (14.2.5)-(14.2.6));
3. a rectangular contour shift and balancing of the vertical and horizontal edge errors
   (Theorem 14.25(A)).

Titchmarsh proves the RH specialization and pointwise convergence. Balazard-Saias supplies the
stronger uniform `N^(-delta/3) (1+|Im(s)|)^eta` estimate under zero-freeness in `Re(s) > alpha`.
This batch does not identify the two statements.

## Pinned-Library Boundary

Pinned mathlib contains:

- `Complex.borelCaratheodory`;
- `Complex.HadamardThreeLines`;
- rectangle Cauchy-Goursat integral identities;
- `Complex.exists_continuousOn_eqOn_exp_comp`, which supplies a continuous logarithm branch for a
  continuous nonvanishing function on a simply connected open set.

It does not expose a theorem upgrading that continuous branch to a holomorphic branch. This is the
first missing source-proof edge needed before Titchmarsh's Borel-Caratheodory argument can be
formalized for zeta.

## Sole Lean Target

Prove, without `sorry`, `admit`, or a new axiom, a generic theorem of the following mathematical
content:

```text
If U is open and simply connected, g is holomorphic on U, and g never vanishes on U,
then there is a holomorphic f on U such that exp(f(z)) = g(z) on U.
Moreover f'(z) = g'(z) / g(z) on U.
```

The proof must upgrade the existing continuous lift locally through the complex exponential; it
must not assume the desired analytic logarithm as a premise.

## Classification Rules

- `HARD_GAP_REDUCED`: only if this theorem is used to compile a strictly smaller replacement for a
  named Balazard-Saias source-proof dependency and the fixed assumption frontier moves.
- `DEPENDENCY_GAP_IDENTIFIED`: if the analytic logarithm edge compiles and leaves the next exact
  source edge as the Borel-Caratheodory/subpower reciprocal-zeta estimate.
- `FORMALIZATION_ONLY`: if only supporting interfaces or local corollaries compile.
- `NO_PROGRESS`: if the analytic logarithm target does not compile.

## Assumption Frontier Before

`BalazardSaiasEstimate` remains an explicit unproved proposition. The project has no checked
analytic logarithm branch for zeta on its zero-free half-plane, no reciprocal-zeta subpower bound,
and no truncated Perron theorem matching Titchmarsh Lemma 3.12.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; the continuation summary was checked against the clean
  worktree, `HANDOFF.md`, the target ledger, and the fixed hard-gap DAG before this registration.

## Lean Result

New module: `LeanLab/Riemann/AnalyticLogBranch.lean`.

- `Complex.exists_differentiableOn_eqOn_exp_comp_of_isSimplyConnected` upgrades mathlib's
  continuous logarithm lift to a holomorphic branch and proves the pointwise derivative formula
  `f'(z) = g'(z) / g(z)`.
- The proof is local and does not assume an analytic lift: continuity puts both candidate lifts in
  a strip of imaginary width less than `2*pi`, where injectivity of `Complex.exp` identifies the
  continuous lift with `f(z) + Complex.log (g(w) / g(z))`.
- `LeanLab.Riemann.exists_riemannZeta_differentiableLogBranch` applies the generic theorem to zeta
  on any simply connected open domain that explicitly avoids the pole at `1` and is explicitly
  zero-free.

Both the generic theorem and the zeta specialization compile without placeholders. No theorem in
this batch asserts `BalazardSaiasEstimate` or a reciprocal-zeta growth bound.

## Gap Accounting

- `hard_gap_before`: `G2/F1/Balazard-Saias` was the fixed missing forward theorem.
- `hard_gap_after`: `G2/F1/Balazard-Saias` remains the fixed missing forward theorem.
- `hard_gap_delta`: `0`.
- `assumption_frontier_before`: no checked analytic logarithm branch for zeta on a zero-free,
  pole-free domain; no reciprocal-zeta subpower bound; no matching truncated Perron theorem.
- `assumption_frontier_after`: the analytic logarithm branch and its logarithmic derivative are
  checked. The next exact source edge is Titchmarsh 14.2's Borel-Caratheodory/Hadamard derivation of
  a subpower reciprocal-zeta bound on an interior zero-free region. The truncated Perron theorem
  and contour-error balance remain after that.

## Classification

`DEPENDENCY_GAP_IDENTIFIED` with `hard_gap_delta = 0`. The source-proof dependency graph is now
strictly more precise and its first analytic edge is checked, but the quantitative Mobius estimate
itself is unchanged.

## Verification

- `lake env lean LeanLab/Riemann/AnalyticLogBranch.lean`: passed.
- `lake env lean LeanLab/Riemann/AxiomsAudit.lean`: passed; both new theorems depend only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build`: passed, 8601 jobs.
- `sorry`/`admit` scan over project and vendored Lean sources: empty.
- explicit `axiom`/`constant`/`opaque` declaration scan: empty.
- `git diff --check`: passed.
