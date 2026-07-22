# H13 Dirichlet-Family Inclusion Definition Alignment

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01`

Production module: `LeanLab/Riemann/DirichletFamilyInclusionAudit.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Source-to-Lean object map

| Source or route object | Lean object | Alignment |
| --- | --- | --- |
| Riemann zeta | `Complex.riemannZeta` | Mathlib analytic continuation used throughout the project. |
| Open critical strip | `InCriticalStrip s` | Exactly `0 < s.re` and `s.re < 1`; boundary zeros are excluded. |
| Critical line | `OnCriticalLine s` | Exactly `s.re = 1 / 2`. |
| Zeros of a generalized function in the strip lie on the line | `criticalStripZerosOnLine f` | Quantifies only over points where `f s = 0` and `InCriticalStrip s`. It asserts no analyticity, functional equation, or Euler product for generic `f`. |
| Dirichlet L-function | `DirichletCharacter.LFunction chi` | Mathlib's analytic continuation of a Dirichlet L-series. |
| Riemann zeta as the modulus-one member | `DirichletCharacter.LFunction_modOne_eq` | Exact function equality at Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; no project surrogate is introduced. |
| All-Dirichlet critical-strip claim | `allDirichletCriticalStripZerosOnLine` | Quantifies over every modulus with `[NeZero N]` and every Mathlib Dirichlet character modulo `N`. |
| A generalized product containing zeta | `fun s => riemannZeta s * g s` | Generic factorization interface only; no Dedekind, Rankin--Selberg, or automorphic identity is asserted. |
| Extra-factor obstruction | `fun s => riemannZeta s * (s - (1 / 4 : Complex))` | The factor has an exact root at `1/4`, which lies in the open strip but off the critical line. It is not an L-function. |

## Exact theorem directions

`criticalStripZerosOnLine_riemannZeta_iff` proves both directions. For the forward direction, the
project's compiled theorem `nontrivial_zero_re_pos` and `nontrivial_zero_re_lt_one` put every
nontrivial zeta zero in the open strip. For the reverse direction, a strip zero cannot be a
negative even trivial zero and cannot be `1`, so Mathlib's RH predicate applies.

`criticalStripZerosOnLine_dirichletL_modOne_iff` transports that equivalence through the exact
Mathlib modulus-one function equality. No primitive-character, Euler-product, or functional-
equation premise is added.

`riemannHypothesis_of_allDirichletCriticalStripZerosOnLine` specializes the family claim to
modulus one. This is a reduction from a stronger statement, not evidence that the stronger
statement is easier.

`criticalStripZerosOnLine_riemannZeta_of_mul` and
`riemannHypothesis_of_criticalStripZerosOnLine_riemannZeta_mul` use only `0 * g(s) = 0`. They prove
one-way inheritance from product zero control to zeta zero control.

`not_criticalStripZerosOnLine_riemannZeta_mul_offLineFactor` proves that arbitrary product
enlargement does not preserve an RH-equivalent zero set: the extra factor inserts the exact
off-line strip zero `1/4`, independently of the value of zeta there.

## Claim boundary

- No generalized RH, Dirichlet GRH, automorphic RH, or Dedekind-zeta RH input is proved.
- No family average, zero density, trace formula, converse theorem, or functorial transfer is used.
- No p-adic L-function, Iwasawa module, characteristic ideal, or map to complex zeta zeros is
  constructed.
- The generic extra-factor witness is not the Davenport--Heilbronn function and has no Euler
  product.
- The compiled result closes only the directionality and inclusion logic of H13. The exact open
  node remains a theorem controlling every zero of the individual zeta function from a proved
  generalized, automorphic, family, or p-adic mechanism.

## Kernel and trust audit

- Production module direct compile: pass with no warning.
- Exact TargetChecks: eight, all pass.
- Registered Targets: one proven transfer-audit node and one in-progress individual-transfer node.
- Selected axiom prints: seven; each depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Production forbidden scan: empty for `sorry`, `admit`, `native_decide`, custom `axiom`,
  `opaque`, and `unsafe`.
- Full build: `8,748` jobs pass; only pre-existing replay warnings are present.
