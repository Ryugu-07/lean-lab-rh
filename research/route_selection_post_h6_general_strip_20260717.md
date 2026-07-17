# Route Selection After General Strip Contraction

Date: 2026-07-17

Previous campaign: `CAMPAIGN-20260717-H6-GENERAL-STRIP-CONTRACTION-01`, publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

Next state: `ROUTE_SELECTION -> LITERATURE`.

## Authoritative frontier

- RH, W2/G7, M2/G3, and H6-E/G8 remain open.
- The exact source-normalized heat family, time-zero xi coordinate, forward preservation,
  half-time upper bound, arbitrary-base strip contraction, simple-zero paths, and regularized
  force law are public Lean theorems.
- Platt--Trudgian Corollary 2 already proves `Lambda <= 0.2`. This is known mathematics, not a new
  quantitative target.
- The general strip theorem now compiles the final de Bruijn step: a global strip of half-width
  `y0` at time `t0` yields all-real zeros at `t0+y0^2/2`.
- The remaining published route to `0.2` consists of Polymath's zero-free-region criterion and
  the three numerical/analytic certificates supplying its initial, final, and barrier regions.

## Candidates compared

| candidate | value | current mechanism | decision |
| --- | --- | --- | --- |
| Polymath zero-free-region criterion | exact structural consumer immediately before the certified `0.2` computation | compiled joint continuity, strict source strip, simple-zero force, and general strip contraction; repeated-zero backward splitting is missing | select |
| Full Platt--Trudgian/Polymath `H_(1/5)` reconstruction | closes the known unconditional `0.2` endpoint | requires the criterion plus a very large zeta-zero verification and rigorous Riemann-Siegel interval stack not yet represented in Lean | retain as the parent campaign frontier, not the first indivisible implementation |
| Strict improvement below `0.2` | genuine new quantitative progress | no fixed replacement barrier, far-region, or verified-height certificates | retain in conjecture pool only |
| W2/G7 unconditional Gaussian-Weil positivity | RH-equivalent direct attack | no new complete-expression cancellation or positivity representation after the prime-kernel obstruction | defer |
| M2/G3 direct Baez-Duarte closure | RH-equivalent direct attack | no new coefficient family or residual estimate beyond the projection, frequency, Gram, and sparse-target obstruction records | defer |
| H1/H2 finite count bridges | useful source-neutral infrastructure | exact finite combinatorics only; cannot exclude one off-line zero | do not select while a source theorem directly adjacent to the H6 quantitative frontier is available |
| H10 curve-divisor development | known function-field infrastructure | no number-field consumer for the Riemann-Roch/Frobenius layers | defer |

## Primary-source audit

Polymath, arXiv `1904.12438`, Theorem 1.2 and Proposition 3.3, use three zero-free regions. The
initial time-zero region prevents entry from the left, the final asymptotic region prevents entry
from the right, and the intermediate barrier prevents a zero from crossing between them. The
conclusion is a global time-`t0` canopy of half-width `y0`, followed by de Bruijn contraction to
`t0+y0^2/2`.

The proof is not a propositional wrapper. At the first boundary-contact time it must:

1. obtain an actual boundary zero by compactness and zero persistence;
2. exclude the vertical sides with the barrier and positivity on the imaginary axis;
3. send a repeated boundary zero backward above the moving canopy using Hermite splitting;
4. send a simple boundary zero backward using the divisor force and the source geometric
   separation estimate.

The project has items 1, 2, and the analytic ingredients of 4 in partial form. It has no
repeated-zero Hermite splitting theorem, and its exported implicit path currently covers simple
real zeros rather than arbitrary complex simple zeros. These are exact dependencies, not reasons
to weaken the endpoint.

Polymath Table 1 uses the row

```text
X = 5*10^12 + 194858,  t0 = 0.186,  y0 = 0.16733,
```

for which `t0+y0^2/2 < 0.2`. Platt--Trudgian note that their verified height exceeds the threshold
needed to activate this row and conclude `Lambda <= 0.2`.

## Selection

Select `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`. The indivisible endpoint is the
source-faithful Proposition 3.3 zero-free criterion composed with the compiled arbitrary-base
strip theorem, plus the exact Table 1 row corollary at time `1/5` under the three explicit region
certificates.

This is known mathematics with expected `hard_gap_delta=0` and
`route_infrastructure_delta=1`. It does not prove any region certificate, `Lambda<=0.2`, H6-E/G8,
or RH unconditionally. Success exposes the exact remaining certified-computation boundary. Local
failure records the first missing analytic theorem as an obstruction and returns the persistent
RH Goal to fresh value-ranked route selection.
