# Route Selection after H12 Top Argument Variation

Date: 2026-07-31

Decision: select
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`.

Selected node: `H12-LM-GLOBAL-INDENTED-COUNT-01`.

## Selection rule

Historical coverage is omission search, not a checklist. A route is valuable when reconstructing
its closest proof chain may expose an overlooked branch, a premise that can be weakened, or an
input already supplied by another route. Original conjectures, falsification, and direct attacks
on RH remain open throughout.

H12 is not selected merely because the preceding campaign was adjacent. The completed top-side
argument-variation theorem materially changes the global Levinson--Montgomery boundary: the
actual `zeta` and `zeta'` top contributions are now simultaneously `O(log(t+2))`, while the
paired-mass branch, vertical signs, critical-zero indentation, common zero-free bottoms, and
left-half-plane winding theorem were already compiled.

## Cross-family comparison

- H1/H2 still require global moment or density estimates that are themselves the deep analytic
  producers of the classical methods.
- H7/H8 still lack an actual spectral object plus a quantitative gap or all-index
  hyperbolicity producer.
- H10 has a live general-curve one-point filtration and Riemann--Roch frontier, but Mathlib does
  not yet provide the source-ready curve divisor infrastructure. A generic valuation-separated
  lemma would be useful but would leave the decisive geometric object uninstantiated.
- H11 still needs an actual PCC/Fujii error producer or a mechanism amplifying sparse
  off-critical exceptions.
- H14 still needs certified interval root isolation, boundary nonvanishing, and a global Turing
  tail.
- H12 now has a concrete omission-sensitive logical gap inside the source branch itself and
  actual compiled inputs on both sides of that gap.

## Omission-sensitive hinge

The existing predicate
`LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n` asserts strict negativity at every
interior point where `zeta` is nonzero. It does not explicitly assert that the horizontal segment
contains no zeta zero.

An interior zero cannot actually survive this condition. Local analytic factorization gives

```text
zeta(s) = (s-rho)^m h(s),  h(rho) is nonzero,
zeta'(s)/zeta(s) = m/(s-rho) + h'(s)/h(s).
```

Immediately to the right of an off-critical zero on the same horizontal line, the principal term
has arbitrarily large positive real part while the residual stays bounded. This contradicts the
negative-height predicate without evaluating the totalized logarithmic derivative at the zero.

If this compiles, the cofinal-negative branch becomes an actual strict-left horizontal geometry:
the open segment is zero-free and derivative-zero-free; at the critical endpoint either zeta is
nonzero or the already compiled multiplicity-aware left semicircle supplies the indentation. The
opposite branch already gives the source linear-density count conclusion.

## Material re-entry

The 2026-07-28 admissible-contour campaign falsified the claim that an arbitrary nonvanishing
bottom has zero winding. This re-entry does not reuse that mechanism. It attacks a source-produced
strict-negative integer-height branch, and it starts only after the actual top variation and
principal-log winding theorem have compiled.

The full endpoint remains:

```lean
theorem levinsonMontgomeryTheoremOne_actual :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy
```

The local zero-exclusion theorem is not a substitute for this endpoint.

## Claim boundary

No count theorem, Speiser equivalence, derivative-zero-free statement, RH, or equivalent premise
may be assumed. A successful full campaign formalizes the known 1974 count theorem and activates
the existing unconditional Speiser-equivalence consumer; it does not prove that `zeta'` is
zero-free and does not prove RH.

Production Lean edits remain closed until the docs-only preregistration passes public Lean Action
CI. The persistent RH Goal remains active.
