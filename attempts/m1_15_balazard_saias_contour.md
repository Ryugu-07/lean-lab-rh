# M1-15 Balazard-Saias Contour Completion

Date: 2026-07-11

Fixed gap: `G2/F1/Balazard-Saias/contour-shifting-and-error-balancing`.

## Sole Target

Under `Mathlib.RiemannHypothesis`, and without a `BalazardSaiasEstimate` premise, prove the
uniform bound

```text
norm(mobiusDirichletPartialSum N s - analyticReciprocalRiemannZeta s)
  <= C * N^(-delta/3) * (1+|Im(s)|)^eta
```

for every `delta,eta>0`, `N>=2`, and `1/2+delta<=Re(s)<=1`, then connect it to the fixed Burnol
transformed-error consumer.

## Source And Endpoint Audit

The route reconstructs Burnol Theorem 1.4 (citing Balazard-Saias Lemma 2) using Titchmarsh
Theorems 14.2 and 14.25(A) plus the already compiled source-specialized truncated Perron formula.
The downloaded file initially labeled as the Balazard-Saias paper was a different Nyman-Beurling
paper, so it was not treated as evidence for the contour details.

The audit found that Mathlib assigns `riemannZeta 1` a finite regularized point value. Therefore
the raw field inverse `(riemannZeta 1)⁻¹` is not the analytic reciprocal appearing in the source,
whose value at the pole is zero. The project now defines

```text
analyticReciprocalRiemannZeta s = (s-1) / zetaPoleRemoved s
```

and proves that it equals the raw inverse away from `s=1` and zeta zeros. The source proposition,
its RH specialization, and the Burnol transformed error were corrected to use this function.

## Compiled Route

1. Prove the analytic reciprocal is holomorphic on the RH half-plane.
2. Define the residue-subtracted contour integrand with `dslope` and derive the exact rectangular
   Cauchy-Goursat identity, including the residue at `w=0`.
3. Identify the right edge with `mobiusTruncatedPerronIntegral` and solve for its difference from
   the analytic reciprocal.
4. Bound the left edge by splitting the logarithmic majorant at height one and integrating the
   exact real powers. This avoids an invalid length-times-supremum estimate.
5. Bound both horizontal edges using the widened RH reciprocal-zeta subpower estimate on
   `1/2+d<=Re(z)<=3`.
6. Set `d=delta/3`, `q=min(delta/12,eta/2)`, `x=N+1/2`,
   `H=1+|Im(s)|`, and `T=x^3*H`. Lean checks the left, horizontal, and truncated-Perron power
   balances separately before assembling them.
7. Combine the three contour edges, the truncated Perron error, and `x>=N`. The case
   `delta>1/2` is vacuous.
8. Feed the compiled estimate into the existing critical-line `3/8` zeta bound to obtain the
   Burnol transformed-error majorant with no `hBS` argument.

## Result

- `RiemannHypothesis.exists_balazardSaias_specialized_bound_compiled` proves the sole target.
- `RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le_compiled` removes the explicit
  `BalazardSaiasEstimate` premise from the fixed forward consumer.
- The general-alpha proposition `BalazardSaiasEstimate` remains encoded but unproved.

`result_class`: `HARD_GAP_REDUCED`.

This removes the contour-shifting/error-balancing subedge and closes the RH-specialized forward
block F1. The reverse base Nyman-Beurling/Baez-Duarte criterion, G1, D, M1 as a full equivalence,
and RH itself remain open.

Full `lake build` passes with 8604 jobs. The incomplete-proof and explicit-declaration scans over
`LeanLab` and `PrimeNumberTheoremAnd` have no matches, and `git diff --check` passes. The two main
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Public CI is recorded after
the batch commit is pushed: commit `25f4117` passes Lean Action CI run `29151912852`, job
`86542626185`, in 2m27s.
