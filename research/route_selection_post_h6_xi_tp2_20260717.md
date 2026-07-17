# Route Selection After Actual Xi-Kernel TP2

Date: 2026-07-17

Previous campaign: `LITERATURE-20260717-H6-XI-KERNEL-TP2-01`, publicly closed.

Next state: `ROUTE_SELECTION -> FALSIFICATION`.

## Authoritative frontier

- RH remains the active project goal.
- H6-E/G8 remains the exact endpoint `deBruijnNewmanAllZerosReal 0`.
- The actual source-normalized Xi kernel now has compiled strict TP2/log-concavity, with both
  full derivative series identified on the real axis.
- TP2 does not imply higher Pólya-frequency order. H6-E/G8, W2/G7, and M2/G3 remain open.
- Generic adjacent-gap continuation, reverse-heat Li transfer, and generic positive-kernel Li
  extrapolation are closed obstruction branches.

## New source correction

Wojciech Michałowski, *On the Pólya Frequency Order of the de Bruijn--Newman Kernel: Certified
Failure at Order Five and the Toeplitz Threshold Phenomenon*, arXiv:2602.20313 (2026), gives the
explicit configuration

```text
u0 = 1/100,  h = 1/20,
M_ij = Phi(abs(u0 + (i-j)*h)),  0 <= i,j < 5,
```

and reports `det(M)<0` using interval arithmetic. The external verification repository is pinned
at commit `675058772f2ba4bf409d114b6082ac9990b78b34`. Its `verify_pf5.py` was reproduced locally
with `mpmath==1.3.0`; it reports midpoint approximately `-1.847236073e-9` and a negative interval.
This reproduction selects the exact target but is not a proof premise.

The source proves no statement about RH and explicitly distinguishes this local PF5 obstruction
from the de Bruijn--Newman constant. It leaves global PF4 open.

## Candidates compared

### C1: Lean-certify the actual PF5 counterexample

Prove the exact full-`tsum` determinant negative at the displayed rational configuration, define
the source-faithful order-five Pólya-frequency predicate, and derive its negation by explicit
ordered witnesses.

Value: converts an external floating interval certificate into a kernel-checked obstruction for
the exact project kernel. It directly tests whether the newly compiled TP2 asset can plausibly
escalate to a total-positivity route. Both success and failure are informative because every
transcendental and tail bound must be exposed.

Decision: **SELECTED**.

### C2: attack global PF4

The source lists global PF4 as open. Even a proof would not by itself imply H6-E, while a proof
attempt would first need the same determinant and exponential-enclosure infrastructure as C1.

Decision: defer until the order-five boundary is independently audited in Lean.

### C3: use TP2 in adjacent-zero dynamics

No source or derived identity currently turns physical-kernel log-concavity into the missing
height-integrated sign of the pair-force remainder. Re-entry now would repeat the exhausted
generic mechanism without a theta-specific bridge.

Decision: defer pending a precise bridge conjecture that survives falsification.

### C4: direct W2/G7 positivity

The fixed-width Gaussian arithmetic criterion is already RH-equivalent, but the prime kernel has
an explicit indefinite direction and no new complete-expression cancellation mechanism emerged
from TP2.

Decision: defer without weakening the exact unconditional sign endpoint.

### C5: direct M2/G3 approximation

No new coefficient family or residual estimate appeared after the projection, ladder-frequency,
Gram, and sparse-target audits.

Decision: defer until a materially new approximation mechanism is available.

### C6: improve the numerical de Bruijn--Newman upper bound

This requires certified global zero exclusion and would improve a positive upper bound without
changing the exact sign gap `Lambda<=0`.

Decision: retain as a later quantitative proof attempt.

## Strength and falsification audit

The selected endpoint is strictly an obstruction theorem. `not PF5` neither proves nor disproves
RH. It blocks only arguments requiring order-five or infinite total positivity of the physical
kernel. Expected `hard_gap_delta=0`, `route_infrastructure_delta=1`, and
`obstruction_map_delta=1` on full success.

The external script, decimal table, and `mpmath.iv` implementation cannot become premises. Lean
must independently prove rational enclosures for all nine `Phi` values, including every omitted
series term, and propagate them through an exact determinant bound. Any mismatch in normalization,
ordering, absolute value, or determinant orientation falsifies the selected certificate and must
be recorded.

## Selection

Open `FALSIFICATION-20260717-H6-XI-KERNEL-PF5-01`. Its indivisible endpoint is the actual negative
full-series determinant together with a source-aligned `not PF5` witness. A rational midpoint
matrix, an unchecked interval program, a finite kernel truncation, or an abstract
negative-determinant-to-not-PF lemma alone does not close the campaign.
