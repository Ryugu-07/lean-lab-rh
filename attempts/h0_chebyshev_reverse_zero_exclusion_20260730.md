# H0 Chebyshev Reverse Zero Exclusion

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN`

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
| 9 | `PREREG_PUBLIC_GATE` | Commit `c9c561aaeeff665db804828663719ee9be0745ae` passed Lean Action run `30522338862`, job `90805348547`, in `1m57s`. | Begin the fixed production implementation. |
| 10 | `MELLIN_HOLOMORPHY` | The natural-number `O(N^r)` premise transports to the floor-error cutoff on the real axis. Local integrability and Mathlib's power-bounded Mellin theorem give genuine complex differentiability on `Re(s)>r`. | Identify the continuation with the existing L-series on `Re(s)>1`. |
| 11 | `COMMON_REGION_IDENTITY` | Exact indicator and set-integral normalization prove that the new Mellin continuation equals `LSeries chebyshevPsiErrorCoeff` on the original absolute-convergence half-plane. | Remove the zeta pole before continuation. |
| 12 | `POLE_REMOVED_ODE` | With `Z=(s-1)zeta(s)`, Lean derives `(s-1)Z'=Z*(1-(s-1)E-Z)` on `Re(s)>1` and continues it through the convex half-plane `Re(s)>r`, including `s=1`. | Exclude zeros without division. |
| 13 | `ANALYTIC_ORDER_EXCLUSION` | At a hypothetical zero of order `m>0`, the left side of the ODE has order `m-1` while the right side has order at least `m`; the finite/infinite multiplier cases both contradict the order identity. | Derive the zero bound and RH implication. |
| 14 | `RH_CONSUMER` | Every nontrivial zero satisfies `Re(rho)<=r` under the fixed-exponent premise. Choosing an exponent strictly between `1/2` and a hypothetical right-half zero, then reflecting `rho` to `1-rho`, proves RH from all positive-epsilon Chebyshev bounds. | Compile the fixed-exponent falsification boundary. |
| 15 | `NEGATIVE_CONTROL` | The explicit witness `r=beta=3/4` satisfies both reflected strip bounds but is off the critical line. One fixed exponent above one half is therefore insufficient. | Register, audit, and run the full build. |
| 16 | `LOCAL_AUDIT` | The 559-line no-sorry module, target ledger, eight exact checks, nine selected standard-only axiom prints, forbidden scans, and full `8814/8814` build pass. | Publish the implementation and freeze immutable evidence. |
| 17 | `IMPLEMENTATION_PUBLIC_GATE` | Commit `247ea4c176505b9186faa51a69f5c53bbdbe80f2` passed Lean Action run `30524180060`, job `90811183408`, in `2m16s`. | Freeze the five Lean blobs and publish docs-only immutable evidence. |

## Current obstruction map

No mathematical premise beyond the displayed Chebyshev error hypothesis is to be introduced.
All five preregistered implementation risks are discharged locally. The remaining mathematical
obstruction is the unconditional producer of the RH-strength Chebyshev error estimate itself.

## Boundary

The campaign is conditional. It does not prove a new prime-number error estimate, does not
assume RH, and does not claim progress on the unconditional RH frontier. It proves that the
displayed family of Chebyshev error estimates is sufficient for RH and makes the exact open
producer explicit.
