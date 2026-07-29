# H1 Hardy--Littlewood Eta Remainder Immutable Evidence

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Classification: `FULL_SUCCESS / HARDY_LITTLEWOOD_LEMMA3_FORMALIZED`

## Frozen implementation

- commit: `e3341491b34959f2b1eb5d4e1fe2f6fc6cb6ac6f`;
- Lean Action run: `30495767931`;
- build job: `90724079010`;
- result: passed in `2m17s`;
- local full build before publication: `8805/8805`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/HardyLittlewoodEtaRemainder.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
```

Their diff from the implementation commit is empty at evidence publication.

## Certified endpoint

`hardyLittlewoodEtaRemainder_endpoint` packages:

- the actual consecutive logarithmic phase ratio;
- denominator separation, inverse norm at most one, and total inverse variation at most one;
- the actual unit-phase block bound `4`;
- the actual eta-block and ordered remainder bound `4*N^(-sigma)`;
- locally uniform convergence and holomorphy on `re(s)>0`;
- identification with `(1-2^(1-s))*riemannZeta(s)` on `re(s)>0`, away from `s=1`;
- the actual critical-line specialization;
- composition with the compiled eta-to-Theta Abel transfer.

Nine exact TargetChecks compile. Nine selected axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Historical finding and boundary

Hardy--Littlewood Lemma 3's eta conclusion does not require the full Fourier-integral proof of
Lemma 2. The direct finite inverse-difference mechanism is sufficient and removes the
`abs(s)` loss from crude adjacent-pair estimates.

This evidence does not certify an eta-error second moment, the source-X mean square, the
Hardy--Littlewood parameter budget, an unconditional linear critical-zero count, H1, or RH.
