# H12 Levinson--Montgomery Left-Half-Plane Winding Final Ledger

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01`

Classification: `FULL_SUCCESS`

Status: `PUBLIC_FINAL_LEDGER_CI_REQUIRED`

## Public chain

1. Docs-only preregistration:
   - commit `a0f051cb09c8ef309cd9458e712adfcf1029851b`;
   - Lean Action run `30402375932`;
   - build job `90420000555`;
   - `1m39s`, success.
2. Frozen implementation:
   - commit `0a1248f2a02fec9d3cf0e774bc6eb4fe8959e0ec`;
   - Lean Action run `30403264392`;
   - build job `90422806378`;
   - `3m4s`, success.
3. Immutable evidence:
   - commit `016f0b50f552ee42126ecf5bf3e93be8edd15e3a`;
   - Lean Action run `30403576041`;
   - build job `90423807382`;
   - `2m11s`, success.

The proof-source diff from the frozen implementation through immutable evidence is empty.

## Compiled endpoint

Lean proves:

- a differentiable strict-left path has the principal-log endpoint formula for its
  logarithmic-derivative integral;
- a closed such path has zero logarithmic winding;
- `SpeiserStrictNegativeHorizontal t` implies the inherited common zero-free condition;
- the exact complex derivative of the actual `zeta'/zeta` ratio;
- the exact real horizontal derivative, with `0 < t` explicitly excluding `s=1`;
- the actual horizontal endpoint formula with integrand
  `logDeriv(zeta')-logDeriv(zeta)`;
- aggregate Target `H12.speiser.left-half-plane-winding`.

## Audit receipt

- 223-line no-sorry production module;
- one proven Target;
- seven exact TargetChecks;
- seven selected axiom prints with only `propext`, `Classical.choice`, and `Quot.sound`;
- empty forbidden scans;
- warning-as-error production and registry compiles;
- local full build `8789/8789`;
- public implementation and immutable-evidence CI green.

## Claim boundary

The result formalizes the exact positive topological step used on page 52 of
Levinson--Montgomery 1974. It does not produce an actual strict-negative horizontal height,
assemble all critical-zero indentations, prove the global argument principle, bound the Jensen
top variation, or prove either count output.

Speiser equivalence, derivative-zero exclusion, H12, and RH remain open.
`historical_route_coverage_delta=1`, `source_topological_bridge_delta=1`, and
`rh_frontier_delta=0`.

## Successor rule

Close only `H12-LM-LEFT-HALF-PLANE-WINDING-01`. Retain
`H12-LM-INDENTED-ARGUMENT-PRINCIPLE-01`,
`H12-LM-JENSEN-TOP-VARIATION-01`, and actual strict-negative height production as open
candidates, but do not select H12 again by inertia.

Return the persistent RH Goal to fresh cross-family historical omission selection after
final-ledger CI. Conjecture generation and direct RH proof attempts remain open.
