# H1 Hardy--Littlewood Eta Remainder Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Classification: `FULL_SUCCESS / HARDY_LITTLEWOOD_LEMMA3_FORMALIZED`

Public state: `EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_PENDING`

## Result

The preregistered endpoint compiles without placeholders as
`hardyLittlewoodEtaRemainder_endpoint` in
`LeanLab/Riemann/HardyLittlewoodEtaRemainder.lean`.

For `s=sigma+i*t`, `sigma>0`, `s!=1`, `1<=N`, and `abs(t)<=N`, Lean proves

```text
norm(
  (1-2^(1-s))*riemannZeta(s)
    - sum_(1<=n<=N) (-1)^(n-1)*n^(-s)
) <= 4*N^(-sigma).
```

The critical-line specialization has the literal exponent `-1/2`. Composing this result with
the previously compiled eta-to-Theta Abel transfer gives an ordered Theta limit with tail

```text
8*(log 2)^(-1)*N^(-re(s)).
```

## Compiled chain

```text
actual alternating logarithmic phase
-> exact consecutive ratio -exp(-i*t*log((n+1)/n))
-> denominator norm at least 1 and inverse norm at most 1
-> total inverse-coefficient variation at most 1
-> every shifted unit-phase block has norm at most 4
-> decreasing-power Abel transfer
-> every finite eta block has norm at most 4*N^(-sigma)
-> ordered eta partial sums are Cauchy
-> canonical ordered limit with the same explicit remainder
-> local uniform convergence and holomorphy on re(s)>0
-> odd/even identification with (1-2^(1-s))*zeta(s) on re(s)>1
-> identity-theorem extension to re(s)>0, s!=1
-> actual project eta remainder, critical-line form, and Theta transfer.
```

## Historical omission result

Hardy--Littlewood derive Lemma 3 by subtracting their Lemma 2 formulas at `x` and `x/2`, where
the two principal terms cancel. The formal reconstruction finds a smaller sufficient
mechanism: the consecutive alternating logarithmic phases have a uniformly separated
difference coefficient whose inverse has total variation at most one.

Thus the full Fourier-integral proof of Lemma 2 is not logically required for the eta
remainder. This is a genuine premise reduction, but it does not bypass the later second-moment
and counting stages of the 1921 proof.

## Closed obstacles

- `OBS-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`;
- `OBS-H1-HARDY-LITTLEWOOD-ETA-SERIES-IDENTIFICATION-01`.

The strict successors are:

- `OBS-H1-HARDY-LITTLEWOOD-ETA-ERROR-MEAN-SQUARE-01`;
- `OBS-H1-HARDY-LITTLEWOOD-X-MEAN-SQUARE-01`;
- `OBS-H1-HARDY-LITTLEWOOD-PARAMETER-BUDGET-01`.

## Local audit

- new production module: 1181 lines;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, heartbeat, or
  recursion-depth relaxation;
- warning-as-error compiles: production module, `Targets.lean`, `TargetChecks.lean`,
  `AxiomsAudit.lean`, and `LeanLab.lean`;
- exact TargetChecks: nine;
- selected axiom prints: nine, each using only `propext`, `Classical.choice`, and `Quot.sound`;
- exact Target registration: one proven target;
- forbidden/resource scans and `git diff --check`: empty;
- full build: `8805/8805`.

## Claim boundary

The implementation does not prove an eta-error second moment, identify and bound the complete
source-coordinate primitive error moment, prove the source-X mean square, close the
Hardy--Littlewood parameter budget, or prove an unconditional linear critical-zero count, H1,
or RH.

The persistent RH Goal remains active.

## Public implementation

Frozen implementation commit `e3341491b34959f2b1eb5d4e1fe2f6fc6cb6ac6f` passed Lean Action
run `30495767931`, build job `90724079010`, in `2m17s`. The five proof and registration files
have an empty diff from that commit at immutable-evidence publication.

Immutable-evidence commit `4994f8bf406f252ed5f6de467cab30faa2254497` passed Lean Action
run `30496035652`, build job `90724980466`, in `1m33s`; the frozen diff remains empty.
