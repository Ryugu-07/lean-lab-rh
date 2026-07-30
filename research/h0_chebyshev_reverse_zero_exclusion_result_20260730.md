# H0 Chebyshev Reverse Zero-Exclusion Result

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN`

## Result

`LeanLab/Riemann/ChebyshevReverseZeroExclusion.lean` is a 559-line no-sorry
implementation of the preregistered reverse Chebyshev--von Koch implication.

Given

```text
psi(N) - N = O(N^r),  0 <= r < 1,
```

Lean constructs the floor-error Mellin continuation

```text
E(s) = s * mellin(floor-error cutoff)(-s)
```

and proves that it is holomorphic throughout `Re(s)>r`. On the common half-plane
`Re(s)>1`, this function is exactly the existing Chebyshev error L-series.

## Pole-Removed Continuation

Writing `Z(s)=(s-1)zeta(s)`, Lean first proves on `Re(s)>1` and then analytically
continues across the whole convex half-plane `Re(s)>r` the identity

```text
(s-1) Z'(s) = Z(s) * (1 - (s-1) E(s) - Z(s)).
```

Both sides are analytic at `s=1`. The continuation therefore crosses the original zeta
pole without introducing a punctured domain and without dividing by zeta at a possible
zero.

## Zero Exclusion

The entire function `Z` is not identically zero, so its analytic order at every point is
finite. If `Z` had a zero of order `m>0` in `Re(s)>r`, the left side of the differential
equation would have order `m-1`, while the right side would have order at least `m`.
Lean compiles the resulting contradiction for both finite and infinite order of the
remaining analytic multiplier.

Consequently:

- `Z(s)` is nonzero throughout `Re(s)>r`;
- every nontrivial zeta zero `rho` satisfies `Re(rho)<=r`;
- if the Chebyshev error bound holds for every exponent `r=1/2+epsilon`,
  `epsilon>0`, then every nontrivial zero has real part at most `1/2`;
- applying the existing reflection theorem to `1-rho` supplies the reverse inequality
  and yields `Mathlib.RiemannHypothesis`.

## Negative Control

Lean exhibits `r=beta=3/4` with

```text
beta <= r,  1-beta <= r,  beta != 1/2.
```

Thus one fixed exponent above one half, even together with reflection symmetry, gives
only a symmetric strip. The every-positive-epsilon quantifier is essential.

## Audit

- warning-as-error compilation passes for the module, `Targets.lean`,
  `TargetChecks.lean`, and `AxiomsAudit.lean`;
- eight exact campaign TargetChecks pass;
- nine selected transitive axiom prints depend only on `propext`,
  `Classical.choice`, and `Quot.sound`;
- placeholder, custom declaration, and resource-relaxation scans are empty;
- full `lake build` passes `8814/8814`, with only inherited warnings.

## Classification

- `result=VON_KOCH_REVERSE_ZERO_EXCLUSION_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `conditional_rh_implication_delta=1`;
- `unconditional_chebyshev_error_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

## Remaining Frontier

This campaign closes the analytic reverse inference under the source error hypothesis.
It does not prove any new unconditional estimate for `psi(N)-N`. The direct H0 frontier
is now concentrated at producing

```text
forall epsilon > 0, psi(N)-N = O(N^(1/2+epsilon))
```

without assuming RH or an equivalent statement. H0 and RH remain open.

## Public Implementation Receipt

Frozen implementation commit `247ea4c176505b9186faa51a69f5c53bbdbe80f2` passed Lean Action
run `30524180060`, build job `90811183408`, in `2m16s`. Immutable evidence is recorded in
`research/h0_chebyshev_reverse_zero_exclusion_evidence_20260730.md`.
