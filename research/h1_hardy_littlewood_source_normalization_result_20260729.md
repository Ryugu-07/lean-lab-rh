# H1 Hardy--Littlewood Source Normalization Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-01`

Node: `H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-ETA-LOWER-01`

Classification: `FULL_SUCCESS / SOURCE_NORMALIZATION_ETA_LOWER_FORMALIZED`

Public state: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_PENDING`

## Compiled result

The 674-line no-sorry module
`LeanLab/Riemann/HardyLittlewoodSourceNormalization.lean` proves:

1. the naive symmetric all-real extension of the source weight is zero at `t=0`;
2. `radius(t)=max |t| 1` is continuous and positive;
3. the repaired source weight is continuous and strictly positive;
4. for `t>=1`, the repaired and literal source weights agree exactly;
5. `sourceX(t)=-sourceWeight(t)*hardyXi(t)` is continuous and has exactly the actual
   nontrivial critical-line zeta zeros;
6. the exact project identity expressing `|hardyXi(t)|` through
   `|Gamma(1/4+i*t/2)|` and `|zeta(1/2+i*t)|`;
7. an explicit Gamma lower estimate for `t>=8`, using the compiled H6
   Stieltjes--Stirling remainder;
8. a positive constant `A_zeta` with
   `A_zeta*|zeta(1/2+i*t)|<=|sourceX(t)|`;
9. continuity of critical-line eta and the factor bound `|eta|<=3|zeta|`;
10. a positive constant `A_eta` with
    `A_eta*|eta(1/2+i*t)|<=|sourceX(t)|`;
11. continuity of the eta integral primitive and its window error;
12. the exact eta primitive interval identity and the absolute-window lower estimate;
13. the lower estimate on `[T,2T]` in the exact premise shape consumed by
    `hardyLittlewood_source_finite_count`.

The aggregate theorem is:

```text
hardyLittlewoodSourceNormalization_endpoint
```

## Cross-route repair

At

```text
z = 1/4 + i*t/2,
```

the H6 theorem
`deBruijnNewmanPolymathGammaStirlingR2_norm_le_three` controls the explicit remainder in the
Gamma expansion. For `t>=8`, elementary norm and argument estimates turn this into a lower
bound for `|Gamma(z)|`. After cancelling the source's
`t^(1/4)*exp(pi*t/4)` factor, the result is a fixed positive zeta comparison.

This is the material reason the node was selected. The constant is a witness, not an
optimization objective.

## Eta window mechanism

Define

```text
eta(s) = (1-2^(1-s))*zeta(s).
```

On the critical line, the complex power has norm `sqrt 2`, hence the compiled coarse bound
`|eta|<=3|zeta|`. Define

```text
F(t) = integral_[0,t] (Re eta(1/2+i*u)-1) du
psi_H(t) = A_eta*(F(t+H)-F(t)).
```

Lean proves exactly

```text
A_eta*H - |psi_H(t)|
  <= integral_[t,t+H] |sourceX(u)| du
```

for `t>=8` and `H>=0`. This is the formerly abstract `ETA-LOWER` premise of the finite count
consumer.

## Negative control

The literal positive-height factor contains `t^(1/4)`. Its symmetric all-real extension has
weight zero at the origin, so positivity cannot justify a global exact-zero adapter.
`hardyLittlewoodRawSourceWeight_zero` compiles this obstruction. The max-|t|-one repair changes
only low height and agrees exactly with the source formula on `t>=1`.

## Audit

- production proof: 674 lines;
- exact TargetChecks: twelve;
- selected axiom prints: nine, each only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, custom axiom, `native_decide`, `opaque`, or `unsafe`;
- no heartbeat, recursion-depth, or resource relaxation;
- warning-as-error checks: module, Targets, TargetChecks, AxiomsAudit, and root pass;
- full project build: `8799/8799`;
- forbidden/resource scans and `git diff --check`: empty;
- frozen five-file proof and registration diff from the implementation commit: empty;
- inherited protected files remain unstaged.

## Claim boundary

This closes the source coordinate normalization and eta absolute-window lower-premise edge in
Hardy--Littlewood 1921.

It does not yet prove:

- equality of the integral primitive with the relevant real component of the Lemma 7 Dirichlet
  series;
- the eta-window error square-mean estimate;
- the actual source-coordinate moving-integral square-mean estimate of Lemma 11;
- the asymptotic parameter budget;
- an unconditional linear count, positive proportion, H1, or RH.

Deltas: historical route coverage `+1`, source logic `+1`, hard gap `0`, RH frontier `0`.

The persistent RH Goal remains active.

## Public chain

- Preregistration commit `65dc6f89905e52deaac1c22a65a2f7ea745a124e` passed Lean Action
  run `30468092999`, build job `90631003060`, in `1m37s`.
- Frozen implementation commit `728acf822fad197fa4f60bd3f89fe502863b830a` passed Lean Action
  run `30468913754`, build job `90633769051`, in `2m43s`.
- Immutable-evidence commit `d3af00a675bf4e99f422a230630e2877a9d266f9` passed Lean Action
  run `30469279435`, build job `90634996505`, in `2m0s`.
- Final-ledger commit `0bb0b20f07717a72fbefb397d5f70e4876f03e57` passed Lean Action
  run `30469539221`, build job `90635882124`, in `2m16s`.

The closure receipt records this chain and closes only the fixed source normalization and eta
lower-premise node.
