# H1 Hardy--Littlewood Eta Primitive Mean Square Immutable Evidence

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`

Classification:
`FULL_SUCCESS / HARDY_LITTLEWOOD_LEMMA7_CONSUMER_FORMALIZED`

## Frozen implementation

- commit: `6245bdbc920be5129442da9cfa8d4df586e2730d`;
- Lean Action run: `30499538237`;
- build job: `90735916929`;
- result: passed in `2m21s`;
- local full build before publication: `8806/8806`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/HardyLittlewoodEtaPrimitiveMeanSquare.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
```

Their diff from the implementation commit is empty at evidence publication.

## Certified endpoint

`hardyLittlewoodEtaPrimitiveMeanSquare_endpoint` packages:

- the canonical ordered logarithmically weighted source series and explicit critical-line
  remainder;
- exact finite source-term/Theta-term alignment and `n=1` cancellation;
- finite real and complex primitive identities;
- separate eta-integral and Theta ordered limit passages, with no termwise infinite
  differentiation;
- the exact eta primitive/source-series imaginary-increment identity;
- the cutoff `N=ceil(3T)`, including `abs(t+u)<=N` and `N<=4T`;
- the uniform shifted source-series `O(T)` mean square for `0<=u<=T`;
- the eta-window ordinary square moment;
- the exact `[T,2T]` restricted-measure `lintegral` consumed by
  `hardyLittlewood_source_finite_count`.

Exact TargetChecks compile. The selected endpoint axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Historical finding and boundary

The public Lemma 3 eta remainder and the weaker finite `O(L+N)` mean-square theorem suffice
for the consumer-strength Lemma 7 upper bound. Hardy--Littlewood Lemma 8's full asymptotic and
the stronger finite `O(N/log N)` saving are not necessary premises for this edge.

This evidence does not certify the source-X moving-window moment, the Hardy--Littlewood
parameter budget, an unconditional linear critical-zero count, H1, or RH.
