# H1 Hardy--Littlewood Eta-to-Theta Abel Transfer Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Status: `FULL_SUCCESS_LOCAL / IMPLEMENTATION_PUBLIC_CI_PENDING`

## Result

The preregistered endpoint compiles without placeholders as
`hardyLittlewoodEtaAbelTransfer_endpoint` in
`LeanLab/Riemann/HardyLittlewoodEtaAbelTransfer.lean`.

For the literal ordered source term

```text
a_s(n) = (-1)^(n-1)*n^(-s),
E_N(s) = sum_(1<=n<=N) a_s(n),
Q_N(s) = sum_(2<=n<=N) a_s(n)/log(n),
```

Lean proves that the eta remainder hypothesis

```text
norm(etaValue-E_N(s)) <= Ceta*N^(-sigma)
```

for every `N>=N0`, with `sigma>0`, `Ceta>=0`, and `N0>=2`, implies the existence of
`thetaValue` such that

```text
Q_N(s) -> thetaValue
```

in natural order and

```text
norm(thetaValue-Q_N(s))
  <= (2/log(2))*Ceta*N^(-sigma).
```

The theorem `hardyLittlewoodTheta_uniform_of_eta_uniform` quantifies over an arbitrary
parameter family. One eta constant uniform over that family therefore gives one Theta constant
uniform over the same family; only the limiting Theta value varies with the parameter.

## Compiled chain

```text
literal source sign
-> exact shifted finite Abel identity
-> positive decreasing reciprocal-log differences
-> exact reciprocal-log telescope
-> two eta remainders bound every unweighted block by 2*Ceta*N^(-sigma)
-> every weighted block is bounded by (2/log 2)*Ceta*N^(-sigma)
-> Theta partial sums are Cauchy
-> Complex completeness supplies the ordered limit
-> the finite block bound passes to the limit
-> parameter-family uniform transfer.
```

## Historical omission result

Hardy--Littlewood Lemma 4 does not need an additional oscillatory estimate beyond Lemma 3.
The reciprocal-log Abel transform preserves the `N^(-sigma)` order. The first genuine analytic
gap is therefore Lemma 3 itself: prove the uniform eta remainder for
`sigma>=sigma0>0`, `abs(t)<A*N` without retaining the extra `abs(s)` factor produced by a crude
termwise derivative estimate.

This is a source-logic localization, not a proof of Lemma 3 and not a numerical-constant
optimization.

## Local audit

- new production module: 488 lines;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, heartbeat, or
  recursion-depth relaxation;
- warning-as-error compiles: production module, `Targets.lean`, `TargetChecks.lean`,
  `AxiomsAudit.lean`, and `LeanLab.lean`;
- exact TargetChecks: five;
- selected axiom prints: six, each using only `propext`, `Classical.choice`, and `Quot.sound`;
- exact Target registration: one proven target;
- forbidden/resource scans and `git diff --check`: empty;
- full build: `8801/8801`.

## Claim boundary

The implementation does not prove the actual Lemma 3 eta remainder and does not identify
`etaValue` with `(1-2^(1-s))*riemannZeta(s)`. It does not identify `thetaValue` with
`hardyLittlewoodEtaPrimitive`, prove the infinite-series error moment, prove the actual
source-X moment, instantiate the count parameter budget, or prove an unconditional linear
critical-zero count, H1, or RH.

The persistent RH Goal remains active.
