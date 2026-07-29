# Route Selection after H2 Classical Detector Inverse Mellin

Date: 2026-07-29

Status: `RERANK_COMPLETE / H1_HARDY_COMPLEX_ALPHA_SELECTED`

## Closed parent

Campaign `LITERATURE-20260729-H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-01` is publicly closed at
closure-receipt commit `51eaa3313b775a7ae1cac5414a1265fb23e8f4cf`. Its frozen implementation
`8c5d820a92178dfd3ad3582e9ffe733a7377bb0e` proves the actual inverse Mellin line and passed
public Lean Action run `30414837829`, build job `90458965005`.

The first remaining H2 edge is now an infinite rectangle contour shift with uniform horizontal
decay for the actual Gamma-Mobius-zeta integrand. Continuing immediately would be route inertia,
so the full historical atlas is compared again.

## User priority applied

The historical survey is an omission search, not a completion count. A route is not treated as
having been tried merely because a paper was listed, an equivalent criterion was stated, or
peripheral infrastructure was compiled. The audit must reach the route's decisive inference,
make every premise visible, and test whether a neglected branch, weakened premise, or input from
another route repairs the failure.

Until the major historical families have received that treatment, this is the default selection
priority. Original conjectures, falsification, and direct attacks on RH remain open at every
stage.

## Cross-family comparison

| family or subroute | first live source edge | omission value | decision |
| --- | --- | --- | --- |
| H1 Hardy 1914 | Bridge the compiled positive-real Cahen-Mellin equation (1) to Hardy's complex-alpha equation (2) on `abs (Re alpha) < pi/2`. | The exact central transition in Hardy's proof is still absent. It requires exponential xi decay, analytic parameter integration, theta-series analyticity, branch-correct positive-real anchoring, and an identity theorem. The compiled equation (1) and conditional Abel-moment consumer lie immediately on its two sides. | **Select.** |
| H12 Levinson-Montgomery | Assemble a multiplicity-aware indented argument principle and top Jensen `O(log T)` variation. | This is central and omission-sensitive, but Mathlib has no ready argument-principle/divisor-integral theorem. The next fixed endpoint would combine a new general complex-analysis layer with several global actual-zeta estimates. | Retain as a high-value successor. |
| H10 Bombieri-Stepanov/Weil | Construct actual curve divisors, Riemann-Roch spaces, intersections, and Frobenius point-count identities. | Finite numerical and spectral hinges compile, but the first missing producer requires broad absent algebraic-geometry infrastructure. | Retain open. |
| H8 de Branges/Conrey-Li | Construct the concrete `F(W)` Hardy space and prove the actual-xi positive shift. | The abstract RKHS continuation consumer compiles; the concrete positive-shift producer is the open source premise and may already carry RH strength. | Retain open. |
| H1 Selberg/Levinson-Conrey | Prove global mollified moments and source zero-count inequalities. | The local sign detector and step geometry compile, but the next inputs are global estimates. Hardy offers a more sharply isolated known theorem first. | Retain open. |
| H2 classical detector | Shift the inverse Mellin line and prove horizontal-edge decay. | Exact and valuable, but adjacent to the just-closed campaign. | Rotate away; retain open. |

## Primary-source lock

The fixed source is G. H. Hardy,
*Sur les zeros de la fonction zeta(s) de Riemann*,
Comptes rendus de l'Academie des sciences 158 (1914), 1012--1014.

- facsimile:
  <https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN>
- corrected page 1012 transcription:
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1014>
- corrected page 1013 transcription:
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1015>

Equation (1) is the compiled positive-real Cahen-Mellin identity. Hardy then sets
`y = pi * exp(i * alpha)` and obtains equation (2):

```text
integral_0^infinity
  (exp(alpha*t) + exp(-alpha*t)) * Xi(2*t) / (1/4 + 4*t^2) dt
= pi*cos(alpha/4)
  - (pi/2)*exp(i*alpha/4)*Theta(pi*exp(i*alpha)).
```

The source range is `-pi/2 < alpha < pi/2` for real `alpha`. The formal continuation naturally
uses the connected complex strip `abs (Re alpha) < pi/2`.

## Why this edge is omission-sensitive

The paper compresses several logically distinct operations into the substitution leading from
equation (1) to equation (2):

1. the critical-line xi integral must tolerate every exponential weight below `pi/2`;
2. the parameter integral must be holomorphic on the full complex strip;
3. the theta series must be holomorphic when `Re (pi*exp(i*alpha)) > 0`;
4. positive real `x` corresponds to `alpha = -i*log x`, so complex powers and exponentials must
   match with the correct branch;
5. equality on that imaginary-axis family must be promoted by a genuine identity theorem on a
   connected domain;
6. evenness of the actual Hardy xi coordinate must give the exact half-line normalization.

None of these may be replaced by direct substitution of a complex number into the existing
real Mellin inversion theorem.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H1-HARDY-COMPLEX-ALPHA-01`.
- `node`: `H1-HARDY-COMPLEX-ALPHA-EQUATION-TWO-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: prove the exponential-weight integrability of the actual
  `hardyXi (2*t)/(1/4+4*t^2)` integrand for every exponent below `pi/2`; prove analyticity of the
  xi integral and theta side on `hardyAlphaStrip`; identify the positive-real equation (1) on
  the imaginary-alpha axis with all branches and constants checked; and prove Hardy's exact
  equation (2) throughout the strip.
- `meaningful_partial`: compile the exponential integrability, both analytic sides, and exact
  imaginary-axis equality, while recording the first failed connected-domain or identity-theorem
  inference exactly.
- `strict_boundary`: no differentiation to all even orders, no tangential theta limit at
  `alpha -> pi/2`, no `HardyXiAbelMomentLaw`, no unconditional Hardy infinitude theorem, no
  critical-zero proportion, no H1, and no RH.
- `production_gate`: no `LeanLab/` edit before the docs-only preregistration passes public CI.

## Selection rationale

This campaign is preferred over a manufactured local lemma because it closes the literal central
transition in the original proof. It also reuses estimates developed in other route families:
H2's Gamma vertical-line machinery and the project's zeta convexity bounds supply the decay
input that was absent when the first Hardy inversion campaign stopped.

The persistent RH Goal remains active.

## Local result

The selected edge reached full local success. `LeanLab/Riemann/HardyComplexAlpha.lean` compiles
the full source strip, both analytic sides, exact theta normalization, branch-correct
imaginary-axis anchor, and `hardyEquationTwo` by the identity theorem. This closes only Hardy
equation (1) `->` equation (2). The tangential theta derivative limit and
`HardyXiAbelMomentLaw` are now the first open H1 source edges.

Frozen implementation commit `0f0cb7c2829dd8c35ccf926e0bfb6a79d75147eb` passed public Lean
Action run `30418152861`, build job `90469028889`, in `3m0s`.
Docs-only immutable evidence commit `389dc3790e2affe3cc6cb7329f78a37cff04023e` passed public Lean
Action run `30418420614`, build job `90469840559`, in `1m56s`.
