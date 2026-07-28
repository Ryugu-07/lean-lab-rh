# Attempt Log: H1 Selberg Local Sign Change

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-SELBERG-LOCAL-SIGN-CHANGE-01`

Status: `FULL_LOCAL_SIGN_CHANGE_PRODUCER_SUCCESS / LOCAL_AUDIT_GREEN`

## Attempt ledger

| step | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_CLOSURE` | Verified the H8 final ledger and public CI. | Commit `84de6e2d13431aa3069d5808b3018eb66f50ccd8`, run `30388546641`, job `90373923787`, passed in `1m52s`. | Return to cross-family selection. |
| `CENSUS_AUDIT` | Compared the H1 prose row with production modules and prior attempts. | Hardy and Levinson-shaped mechanisms have theorem-producing campaigns; Selberg's independent 1942 sign-change method has none. | Split H1 operationally and select the missing subroute. |
| `SOURCE_AUDIT` | Checked Selberg's canonical citation, the 2025 short-mollifier historical distinction, and Iwaniec's description of the squared root mollifier. | The essential local device is a nonnegative square `|N|^2`, not an arbitrary inverse-zeta mollifier. | Freeze a source-faithful local sign detector before global moments. |
| `LOGIC_AUDIT` | Tested whether a zero of the mollified product identifies a zeta zero. | It does not: the root mollifier may vanish. A strict positive/negative pair is safe because a nonnegative multiplier cannot reverse the base signs. | Use a strict integral triangle gap to produce both signs. |
| `NEGATIVE_CONTROL_DESIGN` | Replaced the square by a sign-changing multiplier. | A constant nonzero base times `m(t)=t` changes sign across `[-1,1]`; arbitrary multipliers can manufacture false detections. | Require a compiled countermodel. |
| `API_AUDIT` | Located `hardyXi`, its continuity, and `hardyXi_eq_zero_iff_isNontrivialZero`; checked interval-integral and finite-family infrastructure. | The actual zeta zero dictionary and required real-analysis APIs are present. | Publish preregistration before production edits. |
| `PREREG_PUBLIC_GATE` | Published the docs-only fixed endpoint before Lean production edits. | Commit `18113427dae282e19a8d257360c6ffe318ada9a5`, run `30389770527`, job `90378107379`, passed in `1m51s`. | Open the production gate. |
| `ROOT_MOLLIFIER` | Defined the positive-index finite Dirichlet polynomial and its critical-line norm square. | Continuity and nonnegativity compile; the `n=0` totalized-power defect is absent. | Build the actual mollified Hardy coordinate. |
| `LOCAL_DETECTOR` | Formalized `abs (integral F) < integral (abs F)` on a nondegenerate interval. | For continuous `F`, Lean produces one strict negative and one strict positive value. | Transport both signs through the square. |
| `ACTUAL_ZERO` | Applied the detector to `hardyXi * normSq(rootMollifier)`. | Nonnegativity transports strict signs to `hardyXi`; continuity and `hardyXi_eq_zero_iff_isNontrivialZero` produce an actual critical-line zero strictly inside the interval. | Assemble distinct witnesses. |
| `FINITE_ASSEMBLY` | Applied the actual-zero theorem to strongly separated finite intervals. | Lean constructs an injective family of actual zero ordinates. | Package the endpoint. |
| `NEGATIVE_CONTROL` | Compiled the constant nonzero base with the sign-changing multiplier `m(t)=t`. | The product changes sign while the base never vanishes. | Preserve the square requirement. |
| `LOCAL_AUDIT` | Compiled the module, Targets, TargetChecks, and AxiomsAudit with warnings as errors; ran forbidden scans, diff check, and full build. | 267-line no-sorry module; eight exact checks; eight selected declarations use only `propext`, `Classical.choice`, `Quot.sound`; empty scans; full `8785/8785` build. | Freeze the implementation and require public CI. |

## Frozen boundary

This campaign attempts only the actual local sign-change producer and finite separated-interval
assembly. It does not assume or prove Selberg's global moment estimates, a positive proportion
of critical zeros, H1, or RH.

Failure after the public gate must identify the first unavailable theorem or false implication
and update the obstacle map. No unproved statement may become a premise.

## Result and obstacle

Result: `FULL_LOCAL_SIGN_CHANGE_PRODUCER_SUCCESS`.

The local deterministic implication is complete. The first source-level open edge is not another
constant in the local theorem: it is the global analytic production of many separated intervals
with a strict triangle gap from Selberg's first/absolute/second moment estimates. No such moment
estimate is assumed by the compiled endpoint.

The campaign therefore records a useful exact interface but no positive proportion, H1, or RH
advance. After the public evidence chain, route selection returns to the full historical atlas.
