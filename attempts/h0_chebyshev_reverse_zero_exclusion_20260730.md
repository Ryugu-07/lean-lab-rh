# H0 Chebyshev Reverse Zero Exclusion

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01`

Status: `PREREGISTERED_LOCALLY / PRODUCTION_BLOCKED`

## Attempt log

| step | mode | result | next action |
| --- | --- | --- | --- |
| 1 | `H11_PUBLIC_CLOSURE` | The PCC slow-window diagonal and its arbitrary-fast negative control passed public implementation and immutable-evidence CI. PCC, HMH, sparse-exception exclusion, and RH remain open. | Rerank across non-adjacent historical families. |
| 2 | `USER_RULING` | Historical work is fixed as omission search: reconstruct the closest approach, inspect discarded branches and hidden premise strength, and seek cross-route repairs. Original conjectures and direct proof attempts remain open throughout. | Apply this criterion to the route census. |
| 3 | `CROSS_FAMILY_SELECTION` | H8, H9, and H12 retain major open historical stacks. H0 has a narrower decisive inference left explicitly open by the compiled Chebyshev--Mellin campaign: error cancellation to holomorphic continuation to zero exclusion. | Audit the primary and authoritative source statements. |
| 4 | `SOURCE_AUDIT` | Von Koch's 1902 primary paper is located through EuDML. DLMF 25.16.4 states the exact modern equivalence using `psi(x)-x=O(x^(1/2+epsilon))` for every positive epsilon. | Align the source statement with existing Lean objects. |
| 5 | `LEAN_INVENTORY` | `ChebyshevMellin.lean` supplies exact coefficients, floor-error Mellin values, and the `Re(s)>1` logarithmic-derivative identity. Mathlib supplies Mellin differentiability under power bounds, convex half-plane uniqueness, the entire `zetaPoleRemoved`, and analytic zero-order calculus. | Freeze the complete reverse chain before production edits. |
| 6 | `POLE_REMOVAL_DESIGN` | Rewriting with `Z(s)=(s-1)zeta(s)` turns the meromorphic logarithmic-derivative identity into `(s-1)Z'=Z*(1-(s-1)E-Z)`, analytic even at `s=1`. This avoids a punctured-domain connectedness detour and any division at a zero. | Use analytic order to preregister zero exclusion. |
| 7 | `FALSIFICATION_BOUNDARY` | One fixed exponent `r>1/2` gives only the symmetric band `1-r<=Re(rho)<=r`; `r=beta=3/4` is an explicit off-line witness to that logic. | Require all positive epsilon in the RH endpoint. |
| 8 | `PREREGISTRATION` | The exact Mellin holomorphy, common-region identity, pole-removed ODE, zero-order contradiction, nontrivial-zero bound, RH implication, and negative control are frozen. | Publish docs-only preregistration and await public CI. |

## Current obstruction map

No mathematical premise beyond the displayed Chebyshev error hypothesis is to be introduced.
The first implementation risks, in order, are:

1. transporting the natural-number `O(N^r)` bound to the floor-valued real-axis cutoff;
2. proving local integrability of the monotone Chebyshev term minus the floor term;
3. aligning Mathlib `mellin` with the existing set integral on `Ioi 1`;
4. applying analytic identity uniqueness on `{s | r<Re(s)}`;
5. making the analytic-order contradiction robust when the multiplier on the right has
   arbitrary finite or infinite order.

## Boundary

The campaign is conditional. It does not prove a new prime-number error estimate, does not
assume RH, and does not claim progress on the unconditional RH frontier unless the error
hypothesis itself is later discharged.

