# Route Selection after H9 Franel Rank--Mertens

Date: 2026-07-28

Status: `RERANK_COMPLETE / H1_HARDY_THETA_INVERSION_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H9-FRANEL-RANK-MERTENS-01` is publicly closed at
final-ledger commit `c96b0df5e6aabc705c9deddbe86d9c367c8f8fe2`, Lean Action run
`30373106791`, build job `90321789406`, in `1m36s`.

The frozen implementation reaches the actual ordered Farey rank, the exact pointwise
Mertens discrepancy, the squared remainder-correlation quadratic, and the centered
Farey-to-Dedekind transform. The complete Franel gcd-kernel formula remains open first at
`FareyDedekindThreeTerm`.

## Fresh cross-family comparison

Selection is by historical omission value and the first real mathematical inference, not by
which file is easiest to extend.

| family | first live edge | reading | decision |
| --- | --- | --- | --- |
| H1 Hardy | Derive Hardy's interior theta identity and Abel moment law from Cahen--Mellin inversion. | This is a classical true theorem, not an open conjecture. The project already contains the same theta kernel, the exact xi normalization, and the complete conditional high-moment consumer. | **Select.** |
| H1 mollifier | Prove Farmer's arbitrary-length mollified second moment. | Directly RH-strength and genuinely open; no new long-mean-value input was found. | Retain open. |
| H2 density | Exclude an actual slowly bending bow of off-line zeta zeros. | Direct value is high, but Maynard--Pratt identify the missing arithmetic rigidity and no source theorem currently supplies it. | Retain open. |
| H7 spectral/Weil | Construct the true infinite arithmetic operator and preserve ground-state orientation through the limit. | Finite source blocks are deep; the missing object and convergence theorem remain broad. | Retain open. |
| H10 function field | Realize the finite rigidity package on an actual curve, then find a number-field transfer. | The actual curve layer is available historically, but the transfer to zeta is not. | Retain open. |
| H11 statistics | Amplify or exclude one sparse horizontal exception. | Exact boundary bookkeeping is compiled; the analytic error still loses a fixed exception. | Retain open. |
| H12 Speiser | Assemble the global indented argument principle and `O(log T)` count comparison. | Source-exact and valuable, but the remaining global contour/count theorem is broader than the present Hardy inversion edge. | High-value reserve. |

H1 is not selected by momentum. The Hardy consumer was closed, then the project rotated through
H11, H0, and H9. Those campaigns did not provide a new input for the open mollifier, bow,
spectral-limit, transfer, sparse-exception, or global-count obstacles. They did confirm that the
existing H6 theta infrastructure is mature enough to attack Hardy's omitted analytic bridge.

## Source finding

Hardy 1914 starts from Cahen's Mellin inversion and obtains, for
`-pi/2 < alpha < pi/2`,

```text
integral_0^infinity
  (exp(alpha*t)+exp(-alpha*t))*Xi(2*t)/(1/4+4*t^2) dt
= pi*cos(alpha/4)
  - (pi/2)*exp(i*alpha/4)*Theta(pi*exp(i*alpha)),
```

where

```text
Theta(y) = 1 + 2*sum_{n>=1} exp(-n^2*y).
```

The source obtains this from its equation (1) by setting `y=pi*exp(i*alpha)`. A source-faithful
formal proof has a precise missing bridge:

```text
critical-line xi bound
  -> vertical integrability of the completed Mellin transform
  -> Mellin inversion for positive real y/pi
  -> analytic continuation in the strip |Re(alpha)|<pi/2
  -> Hardy equation (2).
```

On the imaginary alpha-axis, `y/pi` is positive real and Mathlib's Mellin inversion theorem
applies. Both sides are analytic on the connected strip because
`Re(pi*exp(i*alpha))>0` there. The identity theorem then gives the real-alpha source formula.

This reconstruction also exposes two boundary issues that must not be suppressed:

- the open strip is essential; at `alpha=+/-pi/2` the theta series is no longer absolutely
  convergent in its displayed form;
- Hardy's later boundary value is an Abel limit and cannot be replaced by an unproved ordinary
  endpoint integral.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H1-HARDY-THETA-INVERSION-01`.
- `node`: `H1-HARDY-THETA-INVERSION-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: vertical integrability of the actual completed critical-line Mellin
  transform; source-normalized positive-real Mellin inversion; analyticity of the xi-integral
  and theta-series sides on `|Re(alpha)|<pi/2`; the complex strip identity; and the real-alpha
  Hardy equation (2).
- `meaningful_partial`: vertical integrability plus the exact positive-real Cahen--Mellin
  inversion, with the first failed analytic-continuation statement isolated in theorem form.
- `negative_controls`: exact `alpha=0`, conjugation, and alpha-evenness checks; no boundary
  substitution; no assumption of `HardyXiAbelMomentLaw`; no use of an unproved zero table or RH.
- `strict_boundary`: differentiating all orders, the Bohr--Riesz tangential theta limit, the
  full Abel moment law, Hardy's unconditional infinitude theorem, positive proportions, H1, and
  RH remain outside this campaign unless they follow without endpoint drift.
- `production_gate`: no `LeanLab/` edit before the docs-only preregistration passes public Lean
  Action CI.

