# H1 Levinson--Siegel Step Geometry Attempts

Date: 2026-07-29

Campaign: `PROOF-ATTEMPT-20260729-H1-LEVINSON-SIEGEL-STEP-01`

Node: `H1-LEVINSON-SIEGEL-STEP-GEOMETRY-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

## Fixed question

Does the exact Levinson--Conrey source symmetry class permit smooth pointwise approximation to
Siegel's step, and must every increasingly sharp transition pay an unbounded derivative cost?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION / SOURCE_AUDIT` | Conrey 1989 equations `(32)`--`(39)` contain the still-uncompiled counting bridge. The 2025 short-mollifier paper shows that its length-dependent optimizer approaches Siegel's step and explicitly overturns the belief that Levinson's method needs a sufficiently long mollifier. Existing project work proves variational minimality but not this step geometry or its necessary steepness. | Select a bounded structural proof attempt before the global counting and mean-value producers. Use a normalized logistic family as an independent inhabitant of the exact source symmetry class, and a general mean-value theorem as the negative control. |
| 2 | `PREREGISTRATION` | Full, partial, falsification, and claim-boundary criteria are frozen. The logistic family is not the source optimizer, pointwise is not uniform, and no zeta mean value is imported. | Publish docs only. Do not edit `LeanLab/` until public CI passes. |
| 3 | `PREREGISTRATION_PUBLIC` | Docs-only commit `ab02915f8719c6715e0cadd06dcaad9fa7a10a7d` passed public run `30409200376`, job `90441363357`, in `1m30s`. | Open the production gate. |
| 4 | `EXPLICIT_SYMMETRY` | The logistic reflection identity reduces to `exp(-x)=exp(x)⁻¹`. The denominator is exactly `(exp R-1)/(exp R+1)`, hence positive for `R>0`. | Normalize endpoints without changing the reflection class. |
| 5 | `DERIVATIVE_AND_LIMITS` | Mathlib's exponential and inverse derivative APIs prove the exact profile derivative. The three exponential regimes give the left, midpoint, and right pointwise limits. | Record the exact midpoint derivative and prove `R/2 <= |Q_R'(1/2)|`. |
| 6 | `GENERAL_OBSTRUCTION` | The real mean-value theorem supplies an interior derivative equal to the secant slope. A quantitative epsilon-step corollary handles arbitrary positive slope bounds and the negative-bound edge case separately. | Close the no-uniform-slope statement without claiming a polynomial degree theorem. |
| 7 | `LOCAL_AUDIT` | One proven Target, eight exact TargetChecks, seven selected axiom prints, empty production scans, warning-as-error compiles, and full build pass. | Classify `FULL_SUCCESS / STRUCTURAL_OMISSION_GEOMETRY_FORMALIZED`; publish the frozen implementation. |
| 8 | `IMPLEMENTATION_PUBLIC` | Frozen commit `fb5d03e268849dbac7c7d51375d245eba944a92b` passed public run `30410129919`, job `90444149672`, in `2m6s`. The five-file frozen proof/registration diff is empty. | Publish a docs-only immutable-evidence commit; do not modify the frozen set. |

## Current frontier

- `closed_edge`: exact normalized logistic symmetry, pointwise three-case step limit, explicit
  midpoint slope growth, and the general sharp-transition derivative lower bound.
- `proven_target`: `H1.levinson-siegel.step-geometry`.
- `audit`: 319-line no-sorry module; eight exact checks; seven selected prints using only
  `propext`, `Classical.choice`, and `Quot.sound`; full build `8792/8792`.
- `open_after_success`: source optimizer identification, polynomial approximation with
  quantitative control, actual zeta auxiliary counting, mollified mean values, sparse
  exception exclusion, H1, and RH.
- `protected_files`: the six inherited modified/untracked files remain untouched and unstaged.
- `global_goal`: active.
