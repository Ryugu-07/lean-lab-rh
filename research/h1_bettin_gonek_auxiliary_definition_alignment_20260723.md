# H1 Bettin--Gonek Auxiliary Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-AUXILIARY-01`

Status: `LOCAL_MECHANICAL_CLOSURE / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Source coordinates

Primary source: Bettin--Gonek, *The theta=infinity conjecture implies the Riemann hypothesis*,
arXiv:1604.02740, Section 2, especially equations `(2.2)`--`(2.3)`.

For `s=w-1/2+i*t`, the source numerator contains `(s-1) zeta(s)` and the selected-zero
denominator is `s-rho`. The corresponding `w`-plane pole is
`w_rho=rho+1/2-i*t`.

## Object map

| source object | Lean object | alignment |
| --- | --- | --- |
| `s=w-1/2+i*t` | `bettinGonekShiftedArgument t w` | Literal affine complex coordinate. |
| `w_rho=rho+1/2-i*t` | `bettinGonekSelectedPole rho t` | Lean proves substitution returns `rho`. |
| `(s-1) zeta(s)` | `zetaPoleRemoved s` | Existing entire project extension, equal to the source expression away from `s=1`. |
| `(s-1) zeta(s)/(s-rho)` | `bettinGonekCancelledZeta rho s` | Defined as `dslope zetaPoleRemoved rho s`; at a nontrivial zero, this is the canonical holomorphic divided difference and equals the raw quotient away from `rho` and `1`. |
| source `G_t(w)` | `bettinGonekAuxiliaryG rho t w` | Uses the cancelled quotient and retains the exact rational factors `(w-1)^2`, `(w+1)^2`, and `(w+i*t+1)^4`. |
| post-cancellation contour kernel | `bettinGonekJKernel rho t x w` | Exact rational kernel with the selected factor `w-w_rho` isolated. |
| source residue term | `bettinGonekResidueCoefficient rho t x` | Literal coefficient after substituting `w=w_rho`. |

## Holomorphy domain

The paper says `G_t` is holomorphic on `Re(w)>=0`. Holomorphy is formally a local property on an
open set, so Lean proves the stronger neighborhood statement on `Re(w)>-1`. The only remaining
rational denominator zeros are `w=-1` and `w=-1-i*t`, both on the excluded boundary. The zeta pole
and selected-zero denominator are already removed by the divided difference.

Using raw totalized division at `s=rho` would assign a junk value and would not express the source
holomorphic extension. Replacing it with `dslope` is therefore definition alignment, not an added
analytic assumption.

## Selected-pole certificate

Lean proves the punctured-neighborhood limit

```text
(w-w_rho) J_t,x(w) ->
  x^(rho+1/2-i*t) (rho-1)
  / ((rho+3/2-i*t)^2 (rho+3/2)^4).
```

For a nontrivial zero and `x>0`, every numerator and denominator factor is nonzero, so the
coefficient is nonzero. Thus the selected zero really contributes a simple-pole term at this
local algebraic layer; there is no hidden cancellation.

## Claim boundary and next edge

No theorem here proves inverse Mellin support, a uniform bound for `g_t`, vertical decay of `G_t`,
the contour-shift integral identity, the Mellin convolution formula, the residue lower bound after
bounding the shifted integral, Cauchy--Schwarz, the zeta second-moment lower bound, or the complete
moment-to-power bridge.

The next source edge is therefore analytic rather than algebraic: establish enough decay and
integrability to justify the contour movement and control its new vertical integral, or first
compile the source Mellin/convolution identity.

## Mechanical status

- Production module: 277 lines, standalone diagnostic-free compile.
- Targets: one new proven auxiliary target; the full bridge and Farmer moment Targets remain open.
- Exact TargetChecks: 10 new witnesses compile.
- Axiom audit: 7 selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Production forbidden scan: empty.
- Direct compiles: production module, Targets, TargetChecks, and AxiomsAudit pass.
- Full build: 8,752 jobs, passed.
- `rh_frontier_delta=0`; `source_analytic_algebra_delta=1`.
