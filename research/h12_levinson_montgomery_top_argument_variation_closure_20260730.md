# H12 Levinson--Montgomery Top Argument Variation Closure Ledger

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-TOP-ARGUMENT-VARIATION-01`

Node:
`H12-LM-JENSEN-TOP-VARIATION-01`

Status: `CLOSURE_LEDGER / PUBLIC_CI_REQUIRED`

## Public chain

1. Preregistration commit `01a51d79a350f4dd4d9a8bf46bd3458b9ec44ff2` passed Lean Action
   run `30532626405`, build job `90838279704`, in `1m37s`.
2. Frozen implementation commit `adfc63d2d4c33fe3535180a8eac83d6d9e703c50` passed Lean
   Action run `30534415162`, build job `90844126333`, in `2m39s`.
3. Docs-only immutable-evidence commit `631465d872cbbf3f82666b757cc1ee0c14d49df1`
   passed Lean Action run `30534722076`, build job `90845147950`, in `1m59s`.
4. The module, Targets, TargetChecks, AxiomsAudit, and root-import blobs are identical between
   the implementation and evidence commits.

## Closed node

Once this closure ledger passes public CI, close only
`H12-LM-JENSEN-TOP-VARIATION-01`.

The closed edge is:

```text
actual multiplicity-bearing Jensen crossing divisors
-> finite crossing support cardinality
-> local half-plane logarithms on every crossing-free gap
-> continuous top argument variation O(log(t+2))
-> simultaneous bounds at cofinal common zero-free heights.
```

This reconstruction applies to both actual source paths: `zeta'/zeta` and `zeta''/zeta'`.
The phase normalization needed for the derivative crossing count cancels exactly from its
logarithmic derivative.

## Open nodes

- exact bottom orientation for the complementary contour branch;
- the multiplicity-aware global indented argument principle;
- both Levinson--Montgomery global count identities;
- `N_1^-(T)=N^-(T)+O(log T)` and the full dichotomy;
- Speiser equivalence and derivative-zero exclusion;
- H12 and RH.

## Classification

- `result=LEVINSON_MONTGOMERY_ACTUAL_TOP_ARGUMENT_VARIATION_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `generic_crossing_variation_bridge_delta=1`;
- `actual_zeta_top_variation_delta=1`;
- `actual_zeta_deriv_top_variation_delta=1`;
- `global_argument_principle_delta=0`;
- `levinson_montgomery_count_delta=0`;
- `speiser_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

## Rotation rule

This local campaign stops after closure-ledger CI. The next loop must freshly rank the adjacent
global count edge against non-adjacent historical routes. Historical coverage continues as
omission search; original conjectures, falsification, and direct RH proof attempts remain open.

The persistent RH Goal remains active.
