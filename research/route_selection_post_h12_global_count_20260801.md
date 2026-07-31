# Route Selection after H12 Global Count Reduction

Date: 2026-08-01

Decision: select
`PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`.

Selected node: `H14-H12-HEIGHT-TEN-CERTIFICATE-01`.

Open parent: `H12-LM-GLOBAL-INDENTED-COUNT-01`.

## Selection rule

Historical coverage is omission search. A route is selected when its exact surviving edge has
new evidence, a previously unused weakening, or an input now supplied by another route. Formal
convenience and adjacency are not selection reasons. Original conjectures, falsification, and
direct RH attacks remain open.

## Cross-family comparison

| family | exact live edge | present selection value |
| --- | --- | --- |
| H1 | actual Selberg/Levinson global moments or arbitrary-length mollified moments | High RH relevance, but prior audits reduce the next steps to the deep moment producers themselves; no new weakening has appeared. |
| H2 | the fixed short-Mobius twisted fourth moment and the Type-I bow-exclusion branch | Both are exact and open, but three distinct upper-bound shortcuts failed and no new source input has changed that boundary. |
| H7/H8 | actual ground-state rate or concrete half-strip RKHS | Structural value remains high; existing countermodels show that unweighted convergence and absolute Rayleigh excess are insufficient, while the actual source operators remain unavailable. |
| H10 | general-curve one-point pole filtration and Riemann--Roch dimension producer | Important historical coverage, but current Mathlib lacks the source-ready curve/divisor object; another abstract filtration theorem would not instantiate the successful proof. |
| H11 | an actual PCC/Fujii error or sparse-exception amplifier | The density-one mechanism still permits a finite or density-zero off-line orbit; no new source theorem removes it. |
| H14 x H12 | certify the literal height-ten sign and zero-count offset | Newly high leverage: the completed global contour theorem now proves that this finite datum closes the exact count branch and activates the existing Speiser consumer. |

The selected H14 use is not finite-to-global promotion. The global theorem has already reduced
its remaining obligation to one finite certificate. This is precisely the supporting role for
certified computation required by the historical atlas.

## Material change

Before the preceding H12 campaign, a height-ten computation would have been an isolated finite
fact. Lean now proves:

```text
LevinsonMontgomeryHeightTenCertificate
-> LevinsonMontgomeryNegativeExactCountBase
-> LevinsonMontgomeryCountDichotomy
-> full Levinson--Montgomery Theorem 1 conjunction
-> RiemannHypothesis iff SpeiserDerivativeZeroFree.
```

The first implication preserves both actual multiplicity counts while moving to a bottom height
strictly above ten. Every later contour and all-real-cutoff step is compiled. The finite datum is
therefore an actual producer for a named open theorem, not a numerical illustration.

## Source audit

- Levinson--Montgomery 1974, page 52, invokes low-zero information at `t=10` before the exact
  count branch.
- Platt--Trudgian prove rigorous interval verification for actual zeta zeros far beyond height
  ten. Their theorem supplies the computational standard and the zeta-zero component, but it does
  not by itself certify the zeta-derivative count or the horizontal sign of `zeta'/zeta`.
- Johansson's Euler--Maclaurin formulas evaluate the Hurwitz/Riemann zeta function and arbitrary
  derivatives with explicit rigorous remainder bounds. This is the source-faithful candidate for
  a proof-producing evaluator.
- The project independently compiles Hardy--Littlewood's uniform eta remainder on `Re(s)>0`.
  Together with the functional equation and Cauchy estimates, it is a materially different
  fallback evaluator rather than an assumed numerical oracle.

## Navigation-only falsification probe

A high-precision nonrigorous grid was used only to test whether the exact certificate appears
numerically false or has vanishingly small margins. On a coarse grid of
`0 <= Re(s) <= 1/2`, `0.2 <= Im(s) <= 10`, the observed minima were approximately `0.3888` for
`abs(zeta)` and `0.1685` for `abs(zeta')`; the largest observed top-edge real part of
`zeta'/zeta` was approximately `-0.2321`.

These values are not premises, do not appear in any theorem statement, and cannot be promoted to
proof without rational enclosure and a Lean-checked truncation error.

## Fixed endpoint

Full success requires:

```lean
theorem levinsonMontgomeryHeightTenCertificate_actual :
    LevinsonMontgomeryHeightTenCertificate

theorem levinsonMontgomeryTheoremOne_actual :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy

theorem riemannHypothesis_iff_speiserDerivativeZeroFree_actual :
    RiemannHypothesis ↔ SpeiserDerivativeZeroFree
```

The latter two must be obtained by composition from the finite certificate and the already
compiled consumers. This formalizes the classical count theorem and Speiser equivalence; it does
not prove the derivative-zero-free side and does not prove RH.

Production Lean edits remain closed until the docs-only preregistration passes public Lean Action
CI. The persistent RH Goal remains active.
