# H1 Hardy Complex-Alpha Attempts

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-COMPLEX-ALPHA-01`

Node: `H1-HARDY-COMPLEX-ALPHA-EQUATION-TWO-01`

Status: `FULL_SUCCESS / IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_PENDING`

## Fixed question

Can the compiled positive-real Hardy equation (1) be promoted, with every convergence and branch
condition checked, to Hardy's literal equation (2) on `abs (Re alpha) < pi/2`?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | H2 inverse Mellin is publicly closed and its next contour shift is broad. H12's next source theorem needs a new global argument-principle layer. H1 has two compiled endpoints separated by one exact source transition. | Select Hardy's complex-alpha equation (2) after a fresh cross-family comparison. |
| 2 | `SOURCE_RECHECK` | Hardy 1914 pages 1012--1013 pass from positive-real equation (1) to equation (2) by `y=pi*exp(i*alpha)`, then differentiate and take a tangential theta limit. | Lock this campaign to equation (2); keep differentiation and the boundary limit outside the endpoint. |
| 3 | `CROSS_ROUTE_AUDIT` | The earlier Hardy campaign stopped because its uniform xi bound gave only rational integrability. The project now has polynomial critical-line zeta bounds plus Gamma exponential machinery proved in H2/H12 campaigns. | Attempt an actual xi exponential majorant, not an assumed decay interface. |
| 4 | `LIBRARY_AUDIT` | Mathlib supplies parameter-integral differentiation and analytic identity theorems; the project already defines the complex theta series, alpha strip, and xi integral. | Require local uniform domination, real-theta normalization, imaginary-axis anchoring, and connected-strip continuation. |
| 5 | `PREREGISTRATION` | Full, meaningful-partial, falsification, source-normalization, and claim-boundary criteria are fixed. | Publish docs only and await public CI before any `LeanLab/` edit. |
| 6 | `PUBLIC_GATE` | Preregistration commit `ef1752a44ca1b3242348e7ac40ac4b50529b0efe` passed Lean Action run `30415933876`, build job `90462332932`, in `1m37s`. | Open the production gate without changing the fixed endpoint. |
| 7 | `DECAY` | The half-line Gamma identity retains the exact `exp(-(pi/2)|t|)` rate. Transport from `Re z=1/2` to `Re z=1/4` costs only a polynomial, and the compiled critical-line zeta estimate is polynomial. | Prove actual Hardy-xi integrability for every exponential weight `a<pi/2`; do not shrink the source strip. |
| 8 | `PARAMETRIC_INTEGRAL` | Spare strip width absorbs every natural polynomial weight. The first derivative in alpha is dominated by `2*|t|*hardyXiExponentialWeight a t`. | Move the derivative under the restricted half-line integral and compile `analyticOnNhd_hardyXiInteriorIntegral`. |
| 9 | `THETA_NORMALIZATION` | Mathlib's one-variable Jacobi theta already has the exact `1+2*sum_{n>=1}` expansion. The map `alpha -> I*exp(I*alpha)` lands in the upper half-plane exactly on Hardy's strip. | Identify `hardyThetaSeries` with `jacobiTheta`, prove its strip analyticity, and check the positive-real `evenKernel` normalization. |
| 10 | `IMAGINARY_ANCHOR` | For `x=exp(-y)`, the principal real branch gives the exact factors `exp(y/2)` and `exp(y/4)`. Splitting the full line and applying `hardyXi_even` gives the two half-line exponentials with coefficient `2/pi`. | Compile `hardyEquationTwoLeft_imaginary` directly from `hardyCahenMellinInversion`. |
| 11 | `IDENTITY_THEOREM` | Both sides are analytic on the convex strip. The nonzero points `I/(n+1)` approach zero and satisfy the imaginary-axis identity. | Apply `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` and compile `hardyEquationTwo`. |
| 12 | `LOCAL_AUDIT` | The 1,318-line module and all registry files pass warning-as-error checks; five exact TargetChecks compile; five new axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`; scans and `git diff --check` are empty; full build passes `8795/8795`. | Classify the fixed endpoint as full success, freeze the five implementation files, and seek public CI. |
| 13 | `PUBLIC_IMPLEMENTATION_GATE` | Frozen implementation commit `0f0cb7c2829dd8c35ccf926e0bfb6a79d75147eb` passed Lean Action run `30418152861`, build job `90469028889`, in `3m0s`; its five-file proof/registration diff remains empty afterward. | Publish the immutable evidence ledger without changing proof source. |
| 14 | `IMMUTABLE_EVIDENCE_GATE` | Docs-only evidence commit `389dc3790e2affe3cc6cb7329f78a37cff04023e` passed Lean Action run `30418420614`, build job `90469840559`, in `1m56s`; the frozen proof-source diff remains empty. | Publish the final ledger, then issue a closure receipt after its public CI. |

## Current frontier

- `compiled_left_endpoint`: `hardyCahenMellinInversion`, equation (1) for every positive real
  `x`.
- `fixed_campaign_endpoint`: actual exponential integrability, both analytic strip functions,
  exact imaginary-axis anchoring, and `hardyEquationTwo`; all compile.
- `compiled_right_consumer`: `hardyXiAbelMomentAmplification_endpoint`, conditional on
  `HardyXiAbelMomentLaw`.
- `still_open`: even-order differentiation under the integral, tangential theta derivative
  limits, the Abel-moment law, unconditional Hardy infinitude, critical-zero proportions, H1,
  and RH.
- `historical_role`: attack a suppressed central inference in a fixed human proof chain and
  record either the compiled theorem or its first exact obstruction.
- `protected_files`: the six inherited modified/untracked files remain untouched and unstaged.
- `global_goal`: active.

## Result classification

`FULL_SUCCESS / KNOWN_HARDY_1914_COMPLEX_ALPHA_EDGE_FORMALIZED`

The campaign closes only equation (1) `->` equation (2). It does not prove the tangential theta
derivative limit, `HardyXiAbelMomentLaw`, unconditional infinitely many critical-line zeros, H1,
or RH. Historical-route coverage and source-logic deltas are `+1`; RH-frontier delta is `0`.

## Loop metadata

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota; serving budget not exposed.
- `compaction`: inherited summary detected; canonical repository files re-read before selection.
