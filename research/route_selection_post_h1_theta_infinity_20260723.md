# Route Selection after H1 Theta-Infinity Consumer

Date: 2026-07-23

Status: `H1_BETTIN_GONEK_AUXILIARY_SELECTED / PREREGISTRATION_CI_REQUIRED`

## Closed parent campaign

Campaign `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01` is publicly closed at final-ledger
commit `d4196d0f47d42f1c95d29b48dd341b9a469c514b`, public Lean Action run `29968166845`, build job
`89084084918`, in `1m54s`. It proves the real-cutoff interpolation and the final power and
zero-free consumers. The moment-to-power bridge, Farmer's arbitrary-length moment conjecture,
H1, and RH remain open.

## Selection principle

Historical-route coverage is not one campaign per family. The next target should reconstruct a
source mechanism deeply enough to expose a hidden mismatch or shorten an exact RH-relevant edge.
Original conjectures and direct RH attacks remain open, but no unproved statement may become a
premise.

## Candidate comparison

| candidate | present edge | discriminating value | verdict |
| --- | --- | --- | --- |
| Bettin--Gonek auxiliary factor and selected-zero residue | The just-compiled consumer stops exactly before the Mellin, contour, and residue argument. The four-page source gives explicit formulas whose removable singularities and residue coefficient can be checked independently. | A source normalization error would be exposed immediately; success removes the local analytic-algebra layer from the moment-to-power bridge. | `SELECTED` |
| Full Bettin--Gonek moment-to-power theorem | Requires inverse Mellin support, vertical decay, contour shift, convolution, Cauchy--Schwarz, zeta second moment, and uniform constants at once. | Highest H1 value, but too broad for one auditable endpoint before the auxiliary singularities are aligned. | `SUCCESSOR` |
| H7 arithmetic/prolate ratio | The generic Rayleigh-gap consumer is compiled, but the source entries and coefficient vectors are not yet project objects. | High value, but the next ratio-limit claim is model-original and currently has less historical source leverage. | `OPEN` |
| H10 function-field transfer | Finite spectral rigidity is compiled; no number-field cohomology object with a uniform infinite tail is known. | Historically important, but no source theorem currently narrows the transfer to a local check. | `MONITOR` |
| H2/H11 sparse exceptional-zero exclusion | Existing campaigns prove that density and symmetry alone allow sparse exceptions. | A new localizer is still unnamed. | `OPEN` |

This selection is not numerical-bound optimization. It attacks the exact published mechanism by
which one off-line zero is converted into a power obstruction.

## Locked source formula

For `s = w - 1/2 + i*t`, a selected nontrivial zero `rho`, and
`w_rho = rho + 1/2 - i*t`, Bettin--Gonek define

```text
G_t(w) =
  (w-1)^2 (s-1) zeta(s)
  / ((w+1)^2 (s-rho) (w+i*t+1)^4).
```

They assert that this is holomorphic on `Re(w) >= 0`. After multiplying by the source Mellin
transform, the contour integrand becomes

```text
(w-3/2+i*t) x^w
/ ((w+1)^2 (w-w_rho) (w+i*t+1)^4),
```

whose selected-pole coefficient is

```text
x^(rho+1/2-i*t) (rho-1)
/ ((rho+3/2-i*t)^2 (rho+3/2)^4).
```

Primary source: Bettin--Gonek, *The theta=infinity conjecture implies the Riemann hypothesis*,
arXiv:1604.02740, Section 2 and equations `(2.2)`--`(2.3)`.
<https://arxiv.org/abs/1604.02740>

## Formal opening

The project already has an entire `zetaPoleRemoved`, the extension of `(s-1) zeta(s)`. Mathlib's
`dslope zetaPoleRemoved rho` is the canonical holomorphic extension of

```text
((s-1) zeta(s) - (rho-1) zeta(rho)) / (s-rho).
```

At a zeta zero this is exactly the source quotient away from `s=rho`, while remaining defined and
holomorphic at `rho`. It simultaneously handles the zeta pole at `s=1` and the selected-zero
denominator. This is a source-aligned use of mature removable-singularity machinery, not a new
assumption.

## Decision

Preregister campaign `LITERATURE-20260723-H1-BETTIN-GONEK-AUXILIARY-01`. Its fixed endpoint is
the holomorphic auxiliary regularization, equality with the raw source formula off the two
patched points, and the exact nonzero simple-pole coefficient of the contour integrand. Mellin
inversion, decay, contour integration, convolution, moment estimates, the full bridge, Farmer's
conjecture, and RH remain outside this campaign.
