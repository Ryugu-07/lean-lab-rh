# H12 x H1 Low-Zero Paired-Mass Amendment

Date: 2026-08-02

Campaign: `PROOF-ATTEMPT-20260802-H12-H1-LOW-ZERO-MASS-01`

Status: public docs gate passed; amended production theorem compiled locally.

Gate: commit `c45dfa50430a73ed861e7dcd3a93603b391aee7b`, Lean Action run
`30730702585`, build job `91450510326`, `1m46s`.

Global RH Goal: active.

## Reason for amendment

The original `[14,15]` bracket remains a valid sufficient condition, but its Riemann--Siegel
prefactor has a small real projection near the positive endpoint. The already compiled norm
remainder estimate therefore does not decide that endpoint sign. In contrast, the same exact
phase and endpoint-mass machinery has a robust orientation at height `17`.

No navigation value is admitted as a premise. Navigation selected the amended endpoints only;
all production inequalities below must be proved with exact rational bounds.

## Fixed amended target

Prove the actual endpoint signs

```text
0 < hardyXi 10
hardyXi 17 < 0
```

and hence

```text
HardyXiBracketsZero 10 17
```

by the exact Riemann--Siegel contour identity already present in the repository.

## Fixed mass balance

For `13/2 <= y <= 7` and any critical-line zero ordinate `10 <= gamma <= 17`:

```text
selected paired divisor term <= -1/221.
```

Eight exact digamma shifts must prove

```text
archimedean term < 9/2000.
```

The final comparison is exact: `9/2000 < 1/221`.

## Negative endpoint producer

At `y=17`, prove all of the following without a numerical oracle:

1. the total shifted Stirling phase lies in an exact interval that gives
   `prefactor.re < -(4/5) * norm prefactor`;
2. the negative compact half-line mass is bounded by a rational polynomial or exponential
   envelope;
3. the negative tail is integrated by an exact exponential majorant;
4. together with the existing positive endpoint mass, the raw contour integral norm is at most
   `3/4`;
5. the prefactor orientation and remainder norm imply `hardyXi 17 < 0`.

## Success criterion

The amendment succeeds only if Lean compiles:

```text
theorem hardyXi_ten_pos : 0 < hardyXi 10
theorem hardyXi_seventeen_neg : hardyXi 17 < 0
theorem hardyXiBracketsZero_ten_seventeen : HardyXiBracketsZero 10 17
theorem speiserZetaDerivRatio_leftVertical_re_neg_thirteenHalves_seven_lowZeroMass
    {y : Real} (hy0 : 13 / 2 <= y) (hy1 : y <= 7) :
    (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re < 0
```

with exact TargetChecks witnesses, AxiomsAudit entries, no forbidden placeholders, and public
implementation/evidence/receipt CI.

## Falsification and fallback

- If the `y=17` endpoint mass cannot be placed below the fixed phase margin, record the exact
  failed inequality and return to a phase-sensitive real-part integral estimate.
- If eight digamma shifts do not prove `archimedean < 9/2000`, record the exact residual and vary
  the shift count without optimizing beyond what closes `1/221`.
- The original conditional `[14,15]` theorem remains useful and must not be represented as
  disproved.
- The direct reflected finite-subcover producer remains an independent fallback.

## Strict claim boundary

Before the endpoint bracket, mass balance, registries, audits, and public CI all pass, do not claim
the residual left interval, complete boundary, height-ten certificate, H12, or RH.
