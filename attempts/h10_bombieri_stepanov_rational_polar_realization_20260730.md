# H10 Bombieri--Stepanov Rational Polar Realization

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H10-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Goal

Reconstruct Bombieri's pole-order noncancellation in the actual rational function field
`K(t)`, compose it with the compiled descent-kernel producer, and test the strict separation
condition at its equality boundary.

## Attempt log

| step | mode | result | next action |
| --- | --- | --- | --- |
| 1 | `PARENT_CLOSURE` | H7 immutable-evidence commit `61e0a6a64d892c87bce8a2b9c3aa3958e6c3c0e8` passed run `30517299848`, job `90789903323`, in `2m16s`. | Rotate across historical families. |
| 2 | `CROSS_FAMILY_SELECTION` | H10 is the least-covered successful historical family with a concrete algebraic source edge; H1/H2/H7 currently stop at exact deep analytic or spectral producers. | Re-read the source key lemma. |
| 3 | `PRIMARY_SOURCE_AUDIT` | Bombieri and Kedlaya both place polar-order/tensor injectivity before the Riemann--Roch dimension surplus. The existing Lean coefficient-block equivalence is only a model of this dependency. | Search Mathlib for an actual function-field instance. |
| 4 | `MATHLIB_SURVEY` | Mathlib supplies `RatFunc K`, its injective polynomial algebra map, integer degree, and `RatFunc.inftyValuation`; it does not supply a ready general-curve Riemann--Roch theorem. | Select the rational-curve specialization with an explicit general-curve boundary. |
| 5 | `FALSIFICATION_DESIGN` | The source condition `l * pPower < q` has a sharp collision at equality: exponents `(1,0)` and `(0,1)` coincide when `pPower=q`. | Require this negative witness in the fixed endpoint. |
| 6 | `PREREGISTRATION` | Exact positive, negative, valuation, audit, and claim-boundary gates are frozen in `research/h10_bombieri_stepanov_rational_polar_prereg_20260730.md`. | Publish docs-only preregistration and wait for public CI before Lean edits. |

## Current boundary

No production proof has started. The selected endpoint is an actual `K(t)` specialization, not
the general smooth projective curve. Riemann--Roch dimensions, the general polar lemma, the
Bombieri--Stepanov point count, function-field RH composition, number-field transfer, and RH
remain open.

