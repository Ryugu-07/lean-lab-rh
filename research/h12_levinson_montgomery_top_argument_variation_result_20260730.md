# H12 Levinson--Montgomery Top Argument Variation Result

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-TOP-ARGUMENT-VARIATION-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
CLOSURE_LEDGER_CI_REQUIRED`

## Result

`LeanLab/Riemann/LevinsonMontgomeryTopArgumentVariation.lean` is a 946-line no-sorry
implementation of the preregistered crossing-to-continuous-argument bridge and both actual
Levinson--Montgomery top-side instantiations.

## Generic crossing bridge

For a differentiable nonvanishing path `g` on `[a,b]`, suppose every interior point at which
`Re(g(x))=0` belongs to a finite set `S`. Lean proves

```text
abs (Im integral_a^b (g'(x) / g(x)) dx) <= pi * (card S + 1).
```

The proof filters and sorts the arbitrary finite superset. On every crossing-free gap,
intermediate value forces the path into one weak half-plane; the integral is then computed
with either `log(g)` or `log(-g)`. Endpoint crossings and extraneous elements of `S` are
allowed. No global principal-argument subtraction is used.

## Actual source paths

Lean constructs common heights above every prescribed bound at which neither actual zeta nor
its derivative vanishes anywhere on the complete horizontal segment `[0,1]+i*t`.

For both the zeta and phase-normalized derivative Jensen symmetrizations:

1. every real-part crossing is placed in a finite projected divisor-support set;
2. projected cardinality is bounded by complex support cardinality;
3. analyticity makes every support value a positive integer, so support cardinality is at
   most the multiplicity finsum;
4. the preceding Jensen `O(log(t+2))` bounds therefore control continuous argument variation.

The zeta path yields the horizontal integral of `zeta'/zeta`. The derivative normalization
uses the source phase `exp(i*t*log 2)` for crossing counts, while Lean proves that this constant
nonzero phase cancels exactly from the logarithmic derivative, yielding `zeta''/zeta'`.

## Fixed endpoint

Lean proves common constants `C,T0` such that at every sufficiently large admissible height,
both actual top-side logarithmic-derivative integral imaginary parts are bounded by
`C*log(t+2)`. It also proves that such simultaneous bounds occur at admissible heights above
every prescribed real bound.

The registered proven target is:

```text
H12.levinson-montgomery.top-argument-variation
```

with Lean endpoint
`levinsonMontgomeryTopArgumentVariation_endpoint`.

## Audit

- standalone warning-as-error production-module compilation: pass;
- warning-as-error aggregate import, Targets, TargetChecks, and AxiomsAudit: pass;
- exact campaign TargetChecks: nine;
- selected campaign axiom prints: eight, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder and forbidden-declaration scan: empty;
- `git diff --check`: empty;
- full local build: `8816/8816`, inherited warnings only.

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

## Remaining frontier

This closes the crossing-count-to-continuous-argument inference compressed into
Levinson--Montgomery page 52. It does not assemble the multiplicity-aware global indented
argument principle, prove the exact bottom orientation, or derive either global count identity.
The complete Levinson--Montgomery dichotomy, Speiser equivalence, H12, and RH remain open.

Frozen implementation commit `adfc63d2d4c33fe3535180a8eac83d6d9e703c50` passed Lean Action
run `30534415162`, build job `90844126333`, in `2m39s`. Immutable evidence is recorded in
`research/h12_levinson_montgomery_top_argument_variation_evidence_20260730.md`. Docs-only
evidence commit `631465d872cbbf3f82666b757cc1ee0c14d49df1` passed Lean Action run
`30534722076`, build job `90845147950`, in `1m59s`; all five frozen Lean blobs are unchanged.
Final closure-ledger CI remains. After closure, the next route is selected by a fresh
cross-family omission-seeking comparison, not by adjacency.
