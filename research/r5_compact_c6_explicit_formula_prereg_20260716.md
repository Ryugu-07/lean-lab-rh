# R5 Compact C6 Explicit Formula Preregistration

Date: 2026-07-16

Campaign: `CAMPAIGN-20260716-R5-COMPACT-C6-EXPLICIT-FORMULA-01`

## Fixed Frontier

- `node_id`: W1
- `gap_id`: W1c1c2
- `work_class`: FALSIFICATION -> ROUTE_SELECTION -> PROOF_ATTEMPT
- `hard_gap_before`: the complete reflection-symmetrized formula is checked only for compactly
  supported `C-infinity` log-line functions.
- `assumption_frontier_before`: no RH premise, but the current Fourier inversion and first-moment
  proofs pass through a Schwartz wrapper and therefore require infinite differentiability.
- `expected_hard_gap_delta`: one only at the compact finite-regularity subedge.

## Five-Candidate Screen

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: full natural Baez-Duarte inverse-Gram residual estimate | Residual convergence for the exact target is the already compiled RH-equivalent closure statement. Ehm's exact Gram formulas do not supply the missing unconditional residual bound. | Reject. |
| C2: Pyvovarov exponential-damped Mobius approximants | arXiv `2607.12084v1` proves useful fixed-`u` identities but explicitly leaves continuity of the `L2` norm at `u=0` as the difficulty. That continuity is the target-coupling step, not an unconditional bridge. | Reject. |
| C3: complete the raw `IsWeilStripAdmissible` class in its transform supremum | The raw physical carrier is nonseparated because Mellin data ignores the nonpositive half-line. Its bounded strip transform also gives no vertical decay or absolute divisor summability. | Reject. |
| C4: complete compact explicit formula under exactly six continuous derivatives | Six integrations by parts already absorb the compiled fourth-power xi bound. The same decay gives Fourier integrability and an integrable first absolute moment without a Schwartz wrapper. No RH premise is needed. | Select. |
| C5: unconditional compact Weil positivity | The recent Gaussian campaigns already prove the exact reverse separator; an unconditional sign is W2/RH-hard and would repeat that route without a new mechanism. | Reject. |

Primary comparison sources:

- Alexandre Pyvovarov, *A few remarks on the Baez-Duarte Criterion*, arXiv `2607.12084v1`:
  <https://arxiv.org/abs/2607.12084>
- Werner Ehm, *On certain Gram matrices and their associated series*, arXiv `2405.06349`:
  <https://arxiv.org/abs/2405.06349>
- Jean-Francois Burnol, *A lower bound in an approximation problem involving the zeros of the
  Riemann zeta function*, arXiv `math/0103058`:
  <https://arxiv.org/abs/math/0103058>

## Exact Endpoint

```lean
theorem symmetrizedCompactLaplaceXi_arithmetic_explicit_formula_sixContDiff
    {f : R -> C} (hf : ContDiff R 6 f)
    (hfsupp : HasCompactSupport f) {c : R} (hc : 1 < c) :
    (Real.pi : C) * sum' p : RiemannXiDivisorZeroIndex,
        symmetrizedCompactLaplaceWeight f
          (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : C) * symmetrizedCompactLaplaceWeight f 1 +
        compactSymmetrizedXiArchimedeanIntegral f c -
        sum' n : N, compactSymmetrizedVonMangoldtWeight f n
```

The actual Lean source uses the standard Unicode type names already present in the project; this
ASCII display fixes the mathematical type without introducing a documentation encoding dependency.

## Indivisible Proof Batch

1. Replace every use of infinite differentiability in the selected-height sixth-derivative chain
   by finite-order `ContDiff.iterate_deriv'` arguments.
2. Prove Fourier integrability for the exponentially weighted compact density from compact support,
   `C^2`, and inverse-square decay.
3. Prove the first absolute Fourier moment from compact support, `C^6`, and inverse-sixth decay.
4. Use Mathlib's general Fourier inversion theorem, not `HasCompactSupport.toSchwartzMap`, to recover
   both exact physical prime branches and their scaling constants.
5. Reassemble the unchanged finite prime support, pole, GammaR, and multiplicity-bearing divisor
   terms at the exact endpoint.
6. Preserve the old `C-infinity` endpoint as a compatibility corollary.

Helpers alone do not close the campaign.

## Rejection Conditions

Reject the proof attempt if any of the following occurs:

- an RH, zero-location, positivity, or target-closure premise is introduced;
- the new endpoint retains a hidden `ContDiff R infinity f` hypothesis;
- Fourier integrability or the first moment is assumed instead of derived from `C^6` compact support;
- smoothing is used together with an unproved continuity passage;
- the zero sum loses divisor multiplicity, the prime weight changes, or the pole factor changes;
- any `sorry`, `admit`, `native_decide`, project axiom, unsafe declaration, or resource-limit
  relaxation is used.

## Required Evidence

- standalone compilation of the strengthened modules;
- exact `Targets.lean` and `TargetChecks.lean` witnesses for the `C^6` endpoint;
- selected transitive axiom prints with standard axioms only;
- empty forbidden scans and `git diff --check`;
- full `lake build`;
- public implementation CI, immutable evidence backfill, and public closure CI before final closure.

