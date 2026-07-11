# M1 Zeta Convexity Midpoint Batch

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-09`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2/F1/zeta-convexity`
- `work_class`: `FORMALIZATION`
- `status`: complete

### Fixed Success Target

This batch counts as `HARD_GAP_REDUCED` only if Lean compiles, without placeholder proofs or
explicit axioms,

```lean
∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
  ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
    C * (1 + |t|) ^ (3 / 8 : ℝ)
```

or a stronger unconditional exponent below `1/2`.

### Locked Route

1. Extend the compiled asymptotic `13/8` and `9/8` pole-removed edge estimates over the compact
   edge segments by continuity.
2. Use Fiori's corrected analytic symmetrization with integer powers `(13,9)`.
3. Prove its denominator is nonzero on the closed strip and bound both edges by one constant.
4. Prove the quotient satisfies the exact double-exponential `IsBigO` premise of
   `PhragmenLindelof.vertical_strip`.
5. Extract pole-removed midpoint exponent `11/8`, then divide by `|s-1|` to obtain zeta exponent
   `3/8`.

The invalid auxiliary function depending on `re(s)` is forbidden. An abstract strip theorem whose
growth premise remains an assumption does not satisfy the target.

### Classification

- `HARD_GAP_REDUCED`: fixed target compiles and the axiom audit is clean.
- `DEPENDENCY_GAP_IDENTIFIED`: a genuine missing published or library dependency is isolated.
- `FORMALIZATION_ONLY`: only quotient, boundary, compactness, or growth infrastructure compiles.
- `NO_PROGRESS`: no theorem-level boundary improves.

### Runtime

- model: Codex, GPT-5 family; exact backend identifier not exposed
- reasoning effort: not exposed
- budget: unbounded persistent-goal budget; no explicit per-round token budget
- compaction: none since M1-08 completion at preregistration
- result: `HARD_GAP_REDUCED`

## Result

The fixed target compiles as
`LeanLab.Riemann.exists_norm_riemannZeta_criticalLine_le_rpow`. The corrected Fiori quotient,
both whole-edge polynomial bounds, its unconditional double-exponential growth witness, the
Phragmen-Lindelof application, the `11/8` pole-removed midpoint bound, and the final division to
`3/8` are all Lean-checked. No interpolation or growth premise remains assumed.
