# M1 Corrected Zeta Convexity Midpoint

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-09`

## Classification

- `node_id`: `M1`
- `gap_id`: `G2/F1/zeta-convexity`
- `work_class`: `FORMALIZATION`
- `result_class`: `HARD_GAP_REDUCED`
- `hard_gap_before`: F1 requires Balazard-Saias and a critical-line zeta exponent below `1/2`.
- `hard_gap_after`: the zeta-convexity component is closed with exponent `3/8`; Balazard-Saias
  remains the forward F1 gap.
- `hard_gap_delta`: remove `G2/F1/zeta-convexity`; do not remove F1 itself.

## Final Theorem

`LeanLab.Riemann.exists_norm_riemannZeta_criticalLine_le_rpow` states

```lean
∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
  ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
    C * (1 + |t|) ^ (3 / 8 : ℝ)
```

This is unconditional and strictly below exponent `1/2`.

## Proof Route

1. M1-08 supplies pole-removed edge exponents `13/8` and `9/8`.
2. Compact edge segments are absorbed into positive constants using continuity.
3. `holomorphicReflection` implements `z -> conj(f(conj z))` as a holomorphic function.
4. `fioriMidpointQuotient` uses numerator powers `8` and denominator powers `(13,9)`.
5. The denominator is nonzero on the closed strip. The left edge matches exactly; on the right
   edge, monotonicity of `|Q+z|` transfers the four excess powers.
6. The audited global finite-order bound for `(s-1)zeta(s)` yields
   `|K(z)| <= exp(16*C*(2+|Im z|)^2)`. Mathlib's `t^2=o(exp t)` turns this into the exact
   double-exponential `IsBigO` premise of `PhragmenLindelof.vertical_strip`.
7. The midpoint quotient gives a sixteenth-power estimate. Taking the sixteenth root yields
   pole-removed exponent `11/8`; division by `|1/2+it-1| >= |t|` yields `3/8`.

No auxiliary function depends on `re(z)`, and no interpolation or growth statement is assumed.

## Sources And Reuse

- Fiori, *A Note on the Phragmen-Lindelof Theorem*, arXiv `2502.13282`, revised 2026-03-22,
  Theorem 1 and Lemma 5, supplies the corrected analytic symmetrization.
- The finite-order input is from Apache-2.0 `PrimeNumberTheoremAnd`, commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, theorem
  `Complex.zeta_minus_pole_entire_growth`.
- Eleven upstream modules were vendored unchanged and all compiled against this project's Lean
  4.31/mathlib `v4.31.0` environment.

SHA-256 values, in import order:

```text
2ef3c5113ea813e4ea8186cfc977b894e18d89a7d0a284125f41f1e1acacb098  Analysis/Complex/Norm.lean
06551e46c3cd818e0336bf65e4ac5397097acb4b2502c5e04a40b0dd46e7a97e  Analysis/Complex/Trigonometric.lean
a8228ccf1321af80c613c43ffa5868e7cd487f0e5d142c2ed5bc8b355af9ec05  Analysis/SpecialFunctions/Exp.lean
dc81062e1fe9be0839cdf74b5b16dd886f9acc050fe6dfa33cccb47819404fab  Analysis/SpecialFunctions/Gamma/IntegralBounds.lean
397333f5962832871c15edf472e244a22d173a35601f51a82f9615035ccdc16f  Analysis/SpecialFunctions/GammaBounds.lean
350712e09e7bb0acd77c017564038ad18c22cf469d3e44c129e3bcb34d2a57d8  Analysis/SpecialFunctions/Gamma/GammaStirlingAux.lean
ea5a701e53964c60401e1ed00376557fa382e5e8ef8989a15ea752bb8ef40c54  Analysis/SpecialFunctions/Gamma/StripBounds.lean
6859adaca57af1bada5c21a3555334b1849b2368797d9622856158b253b090a9  Analysis/SpecialFunctions/Log/PosLog.lean
eee771e22aa4e6dcd93fc7180e22915afedc70831360a2ace85607b32bd74997  NumberTheory/LSeries/RiemannZetaConvexity.lean
dbc96839d177522e05b40d2b63e1fc4f544fcd85556fc4b2ab10a915cb2d2ef9  NumberTheory/LSeries/RiemannZetaStripBound.lean
fdf1c88850be95d89e75c2fa3e300be5a09e3e80701c3fbd971e875086cc2db2  NumberTheory/LSeries/ZetaFiniteOrder.lean
```

## Assumption Frontier

- `assumption_frontier_before`: sharp edge bounds compiled; corrected midpoint interpolation and
  its interior growth witness absent.
- `assumption_frontier_after`: the complete unconditional `3/8` critical-line theorem is compiled.
  Balazard-Saias remains unformalized and is not assumed.

## Verification

- full `lake build`: passed, 8599 jobs
- exact target witness in `LeanLab/Riemann/TargetChecks.lean`: passed
- trusted-dependency audit: only `propext`, `Classical.choice`, and `Quot.sound`
- `sorry`/`admit` scan over project and vendored Lean sources: empty
- explicit `axiom`/`constant` declaration scan: empty
- vendored SHA-256 identity check: all 11 files match the fixed upstream commit
- `git diff --check`: passed

## Runtime

- model: Codex, GPT-5 family; exact backend identifier not exposed
- reasoning effort: not exposed
- budget: unbounded persistent-goal budget; no explicit per-round token budget
- compaction: none during M1-09
