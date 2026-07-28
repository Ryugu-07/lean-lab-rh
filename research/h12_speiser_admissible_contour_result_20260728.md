# H12 Speiser Admissible-Contour Result

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Classification: `MEANINGFUL_PARTIAL / SOURCE_DEPENDENCY_SPLIT`

## Compiled result

`LeanLab/Riemann/SpeiserAdmissibleContour.lean` proves that every positive-height interval
contains a closed horizontal segment on `0<=Re(s)<=1/2` avoiding zeros of both the actual
Riemann zeta function and its derivative. Such segments occur cofinally.

On every selected segment, both actual logarithmic derivatives are interval integrable. Their
two fixed bottom integrals are bounded by one nonnegative constant. This removes the source's
low-zero-table input from the bottom-error contribution to the `O(log T)` count comparison.

The aggregate certificate is `speiserAdmissibleHorizontal_endpoint`.

## Compiled falsification

The same weakening does not supply the exact-count branch. The source uses
`Re(zeta'/zeta)<0` around the whole closed indented contour to obtain zero winding. Lean proves:

```text
speiserNonzeroWindingModel(0) = speiserNonzeroWindingModel(1),
speiserNonzeroWindingModel(z) != 0,
integral_0^1 logDeriv(speiserNonzeroWindingModel)(x) dx = 2*pi*i.
```

Thus common nonvanishing and matching endpoints do not force zero change of argument.

## Exact remaining edges

For the asymptotic count bound:

- construct the global multiplicity-bearing indented argument principle for zeta and `zeta'`;
- prove the source Jensen `O(log T)` top-edge argument variation.

For the exact-count/dense-count dichotomy:

- prove a fixed strictly negative bottom for the actual zeta logarithmic derivative without an
  unformalized low-zero table, or prove a different zero-winding base-orientation theorem.

`LevinsonMontgomeryLogCountBound`, `LevinsonMontgomeryCountDichotomy`, the complete Speiser
equivalence, derivative-zero exclusion, and RH remain open.

## Mechanical audit

- production module: 270 lines;
- standalone and warning-as-error compiles: pass;
- Target and exact TargetChecks: pass;
- eight selected axiom prints: only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden/custom-declaration/resource-relaxation scans: empty;
- `git diff --check`: pass;
- full build: `8782/8782`;
- frozen implementation: `fbdb2462141e20b169d25eae58ed3c9ef67eb92b`;
- public implementation CI: run `30382486593`, job `90353492533`, passed in `2m7s`;
- proof freeze: empty `LeanLab/` diff from the frozen implementation;
- immutable evidence: `70b437177d7e990319e973bffc36053b413450c0`, run `30382794033`,
  job `90354522762`, passed in `1m41s`;
- final ledger: pending.

## Claim boundary

This is known-route contour infrastructure plus a source-dependency correction. It changes no
unconditional RH frontier and proves neither Levinson--Montgomery Theorem 1 nor Speiser's
criterion in full. The global RH Goal remains active.
