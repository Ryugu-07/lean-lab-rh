# H1 Hardy--Littlewood Eta-to-Theta Abel Transfer Immutable Evidence

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Classification: `FULL_SUCCESS / ETA_TO_THETA_ABEL_TRANSFER_FORMALIZED`

## Frozen implementation

- commit: `f03c6a8f5d35945d34407d0627b7a5f4f629cb9e`;
- Lean Action run: `30479693865`;
- build job: `90670228283`;
- result: passed in `2m17s`;
- local full build before publication: `8801/8801`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/HardyLittlewoodEtaAbelTransfer.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
```

Their diff from the implementation commit is empty at evidence publication.

## Certified endpoint

`hardyLittlewoodEtaAbelTransfer_endpoint` packages:

- the literal Hardy--Littlewood eta term and Theta logarithmic weight;
- the exact shifted finite Abel identity;
- positivity and telescoping of the reciprocal-log differences;
- the eta-block and weighted Theta-block estimates;
- Cauchy convergence of the ordered Theta partial sums;
- the explicit `(2/log 2)*Ceta*N^(-sigma)` remainder;
- preservation of one uniform constant over arbitrary parameter families.

Five exact TargetChecks compile. Six selected axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Historical finding and boundary

Hardy--Littlewood Lemma 4 needs no independent oscillatory estimate beyond Lemma 3. The first
open analytic producer is the actual uniform Lemma 3 eta remainder without an extra `abs(s)`
loss.

This evidence does not certify that remainder, primitive identification, either source moment,
the count parameter budget, an unconditional linear critical-zero count, H1, or RH.
