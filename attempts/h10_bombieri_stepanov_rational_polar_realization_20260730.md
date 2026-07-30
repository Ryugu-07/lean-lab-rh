# H10 Bombieri--Stepanov Rational Polar Realization

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H10-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

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
| 7 | `PREREGISTRATION_PUBLIC_CI` | Commit `e0101629812eb788a6d579e6f5d9b02a4db43fb9` passed Lean Action run `30517894620`, build job `90791696200`, in `1m40s`. | Open production. |
| 8 | `EXPONENT_SEPARATION` | Division by `q` recovers the block index because `i*pPower<q`; positive multiplication cancellation recovers the within-block index. No coprimality premise is needed. | Build the polynomial and rational realizations. |
| 9 | `ACTUAL_FUNCTION_FIELD` | `stepanovRationalPolarRealize` maps the finite source through `K[X]` into `RatFunc K`; exact coefficient recovery proves it injective under the source inequality. | Compose with the descent-kernel producer. |
| 10 | `NONZERO_PRODUCTION` | `exists_stepanovRationalPolar_ne_zero_mem_ker` produces a descent-kernel coefficient family whose rational realization is nonzero whenever the target finrank is smaller. | Check the valued-field interpretation. |
| 11 | `VALUATION_CERTIFICATE` | Every basis vector realizes to the expected power of `RatFunc.X`; its infinity valuation is exactly the exponential of the source polar exponent. | Run the strict-boundary falsification. |
| 12 | `FALSIFICATION` | `stepanovPolar_strict_separation_is_sharp` proves a nonzero two-term source realizes to zero at `l=1`, `pPower=q=1`. | Register and audit. |
| 13 | `LOCAL_AUDIT` | Module, target registry, six exact checks, selected standard-only axiom prints, three forbidden scans, `git diff --check`, and full `8812/8812` build pass. | Publish the frozen implementation. |
| 14 | `IMPLEMENTATION_PUBLIC_CI` | Commit `97b055c30194e61853820ab263d949fd49cc12de` passed Lean Action run `30518731227`, build job `90794240899`, in `2m37s`. | Publish docs-only immutable evidence with frozen Lean blob hashes. |

## Current boundary

The fixed `K(t)` endpoint is locally complete. It is not the general smooth projective curve.
Riemann--Roch dimensions, the general pole-filtration lemma, the Bombieri--Stepanov point count,
function-field RH composition, number-field transfer, and RH remain open.
