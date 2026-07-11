# M1-17 Baez-Duarte Fixed-Epsilon Convergence

Date: 2026-07-11

Fixed gap: `G2/forward/fixed-epsilon-natural-convergence`.

## Sole Target

Under `Mathlib.RiemannHypothesis` and `0 < delta <= 1/2`, prove that the exact source sums

```text
sum_(1<=a<=N) mu(a) * a^(-delta) * rho(1/(a*x))
```

converge in real `L2(0,infinity)` to an element of `baezDuarteKernelClosure`.

## Compiled Route

1. Package the source sums as `baezDuarteMobiusApproxL2` and prove every term lies in the
   positive-natural kernel span.
2. Prove the finite Mellin formula
   `-zeta(s)/s * mobiusDirichletPartialSum N (s+delta)`.
3. Prove `fourier_toLp_eq_toLp_fourier`: for an `L1 intersection L2` function with classical
   Fourier transform in `L2`, Mathlib's abstract `L2` Fourier transform has that representative.
   The proof compares tempered distributions using Fourier-Fubini and the injective `Lp`
   distribution embedding.
4. Identify the weighted-log Fourier transform of each source sum and prove the difference of two
   transforms is the negative difference of the corresponding Burnol transformed errors.
5. Rescale the compiled Burnol majorant from height `t` to Fourier frequency `2*pi*xi`, lift its
   pointwise bound to `L2`, and use Plancherel plus the weighted-log isometry to obtain a Cauchy
   estimate with coefficients `N^(-delta/3)` and `M^(-delta/3)`.
6. Use completeness in complex `L2`, map the limit through real part, and use closedness of the
   natural-kernel closure.

## Result

- `RiemannHypothesis.cauchySeq_baezDuarteMobiusApproxComplexL2` compiles.
- `RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2` compiles the sole target.
- No `BalazardSaiasEstimate` premise, new axiom, `sorry`, or `admit` is used.

`result_class`: `HARD_GAP_REDUCED`.

- `hard_gap_before`: F1 supplied the transformed pointwise error bound, but no theorem said the
  source natural Mobius approximants converge in physical `L2` or have a closure limit.
- `hard_gap_after`: fixed-positive-delta convergence and closure membership are compiled. The
  unconditional `delta -> 0` convergence to the target and final `RH -> closure` assembly remain.
- `hard_gap_delta`: remove only `G2/forward/fixed-epsilon-natural-convergence`.
- `assumption_frontier_before`: classical/L2 Fourier compatibility and Cauchy assembly were absent.
- `assumption_frontier_after`: the target assumes only RH and `0 < delta <= 1/2`; all transform,
  scaling, majorant, and closure steps are checked.

Full `lake build` passes with 8607 jobs. Exact target witnesses, incomplete-proof and explicit-
declaration scans, trusted-dependency audit, and `git diff --check` pass. The compatibility,
Cauchy, and final convergence theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
Commit, push, and public-CI data are appended after publication.
