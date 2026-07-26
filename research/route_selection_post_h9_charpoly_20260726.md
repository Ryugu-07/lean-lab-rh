# Route Selection after H9 Redheffer Characteristic Polynomial

Date: 2026-07-26

Status: `RERANK_COMPLETE / RIESZ_MELLIN_BOUNDARY_SELECTED`

## Closed parent

Campaign `LITERATURE-20260726-H9-REDHEFFER-CHARPOLY-01` is publicly closed at final-ledger
commit `2799ec66850919db744026ae58aaea4c2bd2f769`, Lean Action run `30210035283`, build job
`89814585909`, in `1m37s`. It proves the exact logarithmic characteristic-polynomial
compression and the separate order-one boundary. It proves no estimate for a non-unit root and
no Mertens growth bound.

## Fresh comparison

| candidate | live edge | omission value | decision |
| --- | --- | --- | --- |
| H1 mollifier | Prove Farmer's arbitrary-length mollified moment estimate. | Direct RH-strength analytic input, but no new source-backed mechanism was found in this rerank. | Retain open. |
| H2 density/moments | Exclude the compiled bow countermodel for actual zeta by an arithmetic amplifier. | High frontier value, but the missing amplifier is not supplied by the audited sources. | Retain open. |
| H7 spectral | Prove actual finite-prime ground-state simplicity and convergence to xi. | High structural value, but both uniform spectral gap and limit identification remain open. | Retain open. |
| H8 entire geometry | Promote actual xi hyperbolicity at all indices. | RH-equivalent all-index edge; no new finite-to-global bridge survived the prior audit. | Retain open. |
| H9 Redheffer successor | Bound the logarithmically many non-unit roots. | Source-exact, but an immediate continuation would optimize spectral estimates in the just-used branch. | Rerank below a missing historical branch. |
| H9 Lagarias refinement | Use monotonicity of the 2026 Lagarias auxiliary and minimal-counterexample structure. | The least-counterexample conclusion is weaker than Lagarias's original colossally-abundant reduction. | Reject for this campaign. |
| H9 Riesz criterion | Reconstruct the actual Mobius-exponential kernel and its Mellin continuation boundary. | Classical 1916 route absent from the repository; the modern source states a literal integral on a region that includes a zero-end divergence. | **Select.** |
| H10 function field | Build the actual curve valuation/Riemann--Roch layer or a number-field regularized trace. | High omission value, but a much larger geometric object is still missing. | Retain open. |
| H11 zero statistics | Amplify density-one simple critical zeros to exclude a sparse off-line set. | Directly relevant, but no source-backed absolute-error amplifier was found. | Retain open. |
| H12 Speiser | Assemble the global argument-principle count with certified boundary control. | Literal source route, already deeply reconstructed; the remaining contour assembly stays open. | Retain open. |

## Selected source edge

For

```text
P_2(x) = sum_{n>=1} mu(n) / n^2 * exp(-x / n^2),
```

Riesz's criterion is

```text
RH <-> P_2(x) = O_epsilon(x^(-3/4+epsilon)).
```

Agarwal--Garg--Maji, Lemma 2.4, writes

```text
integral_0^infinity x^(-s-1) P_k(x) dx = Gamma(-s) / zeta(2s+k)
```

in `(1-k)/2 < Re(s) < 1`, excluding `s=0`. For `k=2`, the ordinary integral obtained by
absolute sum-integral interchange has the strip

```text
-1/2 < Re(s) < 0.
```

The right boundary is forced by the zero endpoint: `P_2(0)=1/zeta(2) != 0`, so the displayed
ordinary integral diverges for `Re(s)>=0`. A meromorphic or analytically continued value may
exist there, but it is not the same literal improper integral. The paper's reverse-RH argument
extends the identity to the left and can start from the corrected nonempty strip, so this
boundary issue alone does not refute the Riesz criterion.

## Fixed next campaign

- `campaign`: `LITERATURE-20260726-H9-RIESZ-MELLIN-BOUNDARY-01`.
- `node`: `H9-RIESZ-EXPONENTIAL-MELLIN-BOUNDARY-01`.
- `mode`: `LITERATURE / FALSIFICATION`.
- `positive_endpoint`: actual `k=2` kernel, convergence and continuity, exact value at zero,
  the source Mellin identity on `-1/2<Re(s)<0`, and conditional Mellin convergence and
  holomorphy on `-a<Re(s)<0` from an explicit `O(x^-a)` hypothesis.
- `negative_endpoint`: a kernel-checked witness
  `not MellinConvergent P_2 (-1/2)`, corresponding to source parameter `s=1/2`.
- `strict_boundary`: the Riesz decay, continuation of the product identity into the enlarged
  strip, zero exclusion, RH, and the `k=1` conditionally convergent Hardy--Littlewood kernel
  remain open.
- `production_gate`: no Lean proof-source edit before the docs-only preregistration passes
  public Lean Action CI.

