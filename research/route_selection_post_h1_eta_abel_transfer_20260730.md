# Route Selection after Hardy--Littlewood Eta-to-Theta Abel Transfer

Date: 2026-07-30

Status: `H2_CLASSICAL_DETECTOR_CONTOUR_SHIFT_SELECTED / PREREGISTRATION_LOCAL`

## Closed parent

Campaign `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01` is publicly
closed at receipt commit `524903f18b58322629f38ca7371920adf8d10765`, Lean Action run
`30480635103`, build job `90673552785`, passed in `1m33s`.

The closed node proves that Hardy--Littlewood Lemma 4 has no independent oscillatory input:
the Lemma 3 eta remainder transfers to the logarithmically weighted Theta series by a discrete
Abel transform. The actual Lemma 3 remainder is now the first open source edge in that subroute.

## Selection rule

Historical coverage is an omission search, not an inventory. A route is selected when its
decisive human inference can be reconstructed closely enough to test whether a premise was
unnecessarily strong, a singularity was mishandled, or a missing estimate can now be supplied
from another route.

Original conjectures, falsification, and direct RH proof attempts remain open at every
selection. Numerical optimization is not selected unless a constant crosses a genuine logical
threshold.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H2 classical zero detector | Shift the actual Gamma--Mobius--zeta inverse-Mellin line from `Re(w)=2` to `Re(w)=1/2-Re(rho)`, retain the translated-zeta residue, and make both horizontal edges vanish. | The arithmetic gap, forward transform, inverse line, canceled Gamma pole, and retained local residue compile. The first missing inference is exactly the infinite contour shift used before the Type-I/Type-II dichotomy. Existing rectangle, `dslope`, Gamma-ratio, and zeta-strip machinery may now close it. | **Select.** |
| H1 Hardy--Littlewood Lemma 3 | Prove the uniform eta remainder for `abs(t)<A*N` without an extra `abs(s)` loss. | This is a genuine oscillatory estimate, but immediate re-entry would keep the portfolio inside the just-closed H1 source chain. Retain as the first H1 successor. | Retain open. |
| H1 Selberg / Levinson--Conrey | Produce the global mollified moments and the actual auxiliary-function zero count. | Local consumers compile; the first missing producers remain broad mean-value theorems. | Retain open. |
| H7/H8 spectral | Construct an actual arithmetic operator or concrete xi-bearing RKHS with the required positivity and convergence. | Finite no-go and abstract consumer theorems compile, but the source objects remain broad. | Retain open. |
| H10 function fields | Supply curve Riemann--Roch/intersection geometry or a number-field trace analogue. | Finite spectral rigidity, Hodge, Stepanov, and polar-injectivity consumers compile. The next source edge requires a substantial geometry stack not yet isolated as one theorem card. | Retain open. |
| H11 zero statistics | Produce a statistic that detects even one sparse persistent off-line orbit. | Pair-correlation and moving-window identities tolerate finite or density-zero exceptions; no source-backed amplifier is available. | Retain open. |
| H12/H14 counts and computation | Complete the global argument-principle and certified tail package. | Valuable supporting infrastructure, but not presently a shorter omitted implication. | Retain supporting. |

This H2 re-entry is materially different from the 2026-07-29 inverse-Mellin campaign. That
campaign stopped on the original positive line and proved no rectangle identity. The selected
campaign crosses the actual translated zeta pole and must prove global edge decay and shifted
line integrability.

## Primary-source reconstruction

Primary source:

- James Maynard and Kyle Pratt, *Half-isolated zeros and zero-density estimates*, Appendix C:
  <https://arxiv.org/abs/2206.11729>.

Appendix C takes

```text
M = 2*T^(1/100),  Y = T^(1/2),
I(z) = sum_n a(n)*n^(-z)*exp(-n/Y),
```

writes `I(z)` on an inverse-Mellin line, and for an actual zero
`rho=beta+i*gamma`, `beta>1/2`, shifts to
`Re(w)=1/2-beta`. The shift crosses the translated zeta pole
`w=1-rho`. The Gamma pole at `w=0` contributes no residue because `zeta(rho)=0`.
The resulting retained term is

```text
Y^(1-rho) * Gamma(1-rho) * M(1).
```

Only after this identity does the source compare the coefficient gap and split the remaining
series into dyadic blocks. The selected campaign therefore tests the contour theorem itself;
it does not preregister the later density estimate as already available.

## Fixed next campaign

- `campaign`: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`.
- `node`: `H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `fixed_endpoint`: construct the pole-removed contour weight from
  `dslope zetaPoleRemoved rho`; prove equality with the actual
  Gamma--Mobius--zeta factor away from `0` and `1-rho`; evaluate the exact retained residue;
  prove both horizontal-edge limits and both vertical-line integrability statements; pass the
  finite rectangle identity to the infinite shifted-line formula; compose with
  `classicalDetectorInverseMellinLine`; and expose the coefficient-gap head/tail identity.
- `negative_control`: a conditional contour-shift interface, a local residue limit without
  horizontal decay, or vertical integrability of Gamma alone does not discharge the endpoint.
- `strict_boundary`: no dyadic large-value estimate, Type-I/Type-II density bound, zero-density
  exponent, sparse-exception exclusion, H2 theorem, or RH.
- `production_gate`: no `LeanLab/` proof or registration edit before this docs-only
  preregistration passes public CI.

The persistent RH Goal remains active.
