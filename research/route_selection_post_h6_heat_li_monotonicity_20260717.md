# Route Selection after H6 Heat-Li Time Monotonicity

Date: 2026-07-17

Status: `SELECTED_H6_GENERAL_STRIP_CONTRACTION_PREREG_PENDING_CI`

## Trigger

Campaign `PROOF-ATTEMPT-20260717-H6-HEAT-LI-TIME-MONOTONICITY-01` closed as `NO_PROGRESS`.
The actual-theta conjecture survived numerical screening, but two proof mechanisms stopped at
theta-specific all-index sign control. Governance therefore requires fresh value-ranked route
selection rather than re-entry into the same unsigned convolution or moving-divisor mechanisms.

## Literature correction

The previous H6 census treated `deBruijnNewmanAllZerosReal (1/5)` as an open improvement from
`0.22` to `0.2`. Primary-source review found that Platt and Trudgian, arXiv `2004.09765`, already
prove `Lambda <= 0.2` in Corollary 2. Their verified height exceeds `2.51*10^12`, which activates
the corresponding conditional row in the Polymath barrier table. Therefore H6-Q is known
mathematics awaiting formalization, not an open quantitative attack.

The same Polymath table places `Lambda < 0.19` beyond verified height `10^13`. Because the current
height lies between table rows, a strict improvement below `0.2` is numerically plausible but is
not implied by the published certificates. It remains a conjecture candidate until fresh barrier,
far-region, and zero-count certificates are all produced.

## Value-ranked comparison

| candidate | value | current obstruction | decision |
| --- | --- | --- | --- |
| H6 heat-Li re-entry | would prove RH | unsigned all-index convolution and time-varying divisor transport just failed independently | reject without a new theta-specific mechanism |
| W2/G7 complete Gaussian positivity | would prove RH | termwise prime positivity is formally false; no new global cancellation or norm-square identity survived | defer |
| M2/G3 natural approximants | would prove RH | no new unconditional residual estimate after projection, ladder, and sparse-family audits | defer |
| H6 strict bound below `0.2` | genuine quantitative improvement | candidate parameters and three rigorous numerical/analytic certificates are not yet fixed | retain in conjecture pool only |
| H6 general strip contraction | exact source theorem and exposure dependency for the Polymath criterion | existing proof is specialized to the time-zero width-one strip, but all analytic machinery is compiled | select |

## Selected campaign

Select `CAMPAIGN-20260717-H6-GENERAL-STRIP-CONTRACTION-01` in `LITERATURE` mode. Its indivisible
endpoint generalizes the compiled upper-half theorem from the fixed initial strip at time zero to
an arbitrary source time and squared strip width, and then derives all-real zeros after the exact
additional time `y^2/2`.

This is the final de Bruijn contraction step used after a Polymath canopy certificate. It is
known mathematics and has expected `hard_gap_delta=0`, but it exposes the remaining one-fifth
formalization gap without introducing a numerical premise. Exact preregistration is in
`research/h6_general_strip_contraction_prereg_20260717.md`.
