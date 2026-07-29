# H1 Hardy--Littlewood Finite Mean-Square Immutable Evidence

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Classification: `FULL_SUCCESS / FINITE_MEAN_SQUARE_FORMALIZED`

## Frozen implementation

- commit: `b63bda16e7b899ab88a6ebf12a541f579ab770fe`;
- Lean Action run: `30475443085`;
- build job: `90655877270`;
- result: passed in `2m17s`;
- local full build before publication: `8800/8800`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
```

Their diff from the implementation commit is empty at evidence publication.

## Certified endpoint

`hardyLittlewoodFiniteMeanSquare_endpoint` packages:

- the bounded diagonal coefficient sum;
- the universal linear upper-triangular logarithmic-kernel bound;
- the exact finite shifted norm-square expansion;
- the interval `O(L+N)` theorem;
- the uniform `O(L)` theorem for `N<=L`.

Six selected axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This evidence certifies only the finite polynomial step. Uniform truncation of the conditional
eta series, eta error moment, actual source-X moment, count parameter budget, unconditional
linear count, H1, and RH remain open.
