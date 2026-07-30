# H12 Levinson--Montgomery Jensen Top Zero-Count Closure Ledger

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-JENSEN-TOP-ZERO-COUNT-01`

Node:
`H12-LM-JENSEN-TOP-REAL-ZERO-COUNT-01`

Status: `CLOSURE_LEDGER / PUBLIC_CI_REQUIRED`

## Public chain

1. Preregistration commit `90d078eed410ec31a98df0203cc295a5d1967318` passed Lean Action
   run `30526085450`, build job `90817192932`.
2. Frozen implementation commit `12ddf9bb10f68d3826897bb5403a2ac803da45b0` passed Lean Action
   run `30530385387`, build job `90831064393`.
3. Docs-only immutable-evidence commit `e1c1364405e0d827f8506d9de302e9f8ffd1d735` passed Lean
   Action run `30530768264`, build job `90832307094`.
4. The module, Targets, TargetChecks, AxiomsAudit, and root-import blobs are identical between
   the implementation and evidence commits.

## Closed node

Once this closure ledger passes public CI, close only
`H12-LM-JENSEN-TOP-REAL-ZERO-COUNT-01`.

The closed edge is:

```text
actual zeta and phase-normalized zeta-derivative symmetrizations
-> fixed-strip polynomial growth and center separation
-> multiplicity-bearing Jensen divisor O(log T) counts
-> inclusion of every real top crossing.
```

The source-facing hidden detail is the phase normalization of the zeta derivative. It fixes
the `n=2` Dirichlet term at `-log(2)/2^20`; the complete remaining tail is small enough for a
uniform nonzero center value.

## Open nodes

- `H12-LM-JENSEN-TOP-VARIATION-01`: crossing count to continuous top argument variation;
- admissible cofinal top heights or the complementary strict-negative branch;
- finite indented boundary and multiplicity-aware argument principle;
- the global count identity and `N_1^-(T)=N^-(T)+O(log T)`;
- the full Levinson--Montgomery dichotomy and Speiser equivalence;
- H12 and RH.

## Rotation rule

This local campaign stops after closure-ledger CI. The next loop must freshly rank the H12
argument-variation successor against non-adjacent historical routes. Historical coverage
continues as omission search; original conjectures, falsification, and direct RH proof
attempts remain open.

The persistent RH Goal remains active.
