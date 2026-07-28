# H9 Conrey Actual Seven Flat-Interval Final Ledger

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01`

Classification: `FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS`

Status: `PUBLIC_FINAL_LEDGER_PASS`

## Public chain

1. Docs-only preregistration:
   - commit `37852c81e2d71f1ee95520f62929204f094f34d5`;
   - Lean Action run `30399568275`;
   - build job `90410810937`;
   - `2m19s`, success.
2. Frozen implementation:
   - commit `e259b79773d290435b332c119ad5c81ff0ac16dc`;
   - Lean Action run `30400822025`;
   - build job `90414919121`;
   - `2m55s`, success.
3. Immutable evidence:
   - commit `d629fbd2fdacf1adf866831761f8e127ae3330c7`;
   - Lean Action run `30401127310`;
   - build job `90415928990`;
   - `1m32s`, success.

The proof-source diff from the frozen implementation through immutable evidence is empty.

## Compiled endpoint

For the genuine Legendre character modulo seven, Lean proves:

- the exact period table;
- prefix mass `1` and first moment `0` through `m=3`;
- the all-index discrete sine transform;
- strict positivity of its transform constant;
- exact exponent-two Bernoulli cosine-series evaluation;
- cancellation of all six shifted cosine sums on `[3/7,4/7]`;
- `f_7(x)=0` throughout that interval;
- the irrational zero `sqrt(2)/3`;
- `7 % 8 = 7` and `7 % 8 != 3`.

The result concerns the actual infinite Fourier series. No finite truncation or numerical
approximation appears as a premise.

## Audit receipt

- 428-line no-sorry production module;
- one proven Target and one exact open successor;
- eight exact TargetChecks;
- eight selected axiom prints with only `propext`, `Classical.choice`, and `Quot.sound`;
- empty forbidden scan;
- warning-as-error production and registry compiles;
- local full build `8788/8788`;
- public implementation and immutable-evidence CI green.

## Claim boundary

This campaign proves that Conrey's flat branch is real for a genuine adjacent quadratic
character. It does not refute the contextually scoped Proposition 1 because that proof invokes
Corollary 1 for `q congruent to 3 mod 8`, while the witness is `7 mod 8`.

No source-permitted flat interval or general exclusion theorem is proved. Conjecture 1,
Theorem 3, H9, and RH remain open. The campaign has
`historical_omission_mechanism_delta=1` and `actual_quadratic_character_delta=1`, but
`main_family_flat_branch_delta=0`, `source_refutation_delta=0`, `hard_gap_delta=0`, and
`rh_frontier_delta=0`.

## Successor rule

Close only `H9-CONREY-ACTUAL-SEVEN-FLAT-INTERVAL-01`. Retain
`H9-CONREY-MAIN-FAMILY-FLAT-EXCLUSION-01` as an open candidate, but do not select it by inertia.
Return the persistent RH Goal to fresh cross-family historical route selection after final-ledger
CI. Historical omission search remains the default main allocation; conjecture generation and
direct RH attacks remain open.

## Public final-ledger receipt

Final ledger commit `5dab6664c49e5e03effe9ac309256eaf91e5a171` passed Lean Action run
`30401325481`, build job `90416579015`, in `1m31s`. The proof-source diff from frozen
implementation through final ledger is empty. The local node is publicly closed.
