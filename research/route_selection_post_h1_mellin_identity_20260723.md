# Route Selection after the H1 Mellin Identity

Date: 2026-07-23

Closed parent campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-MELLIN-IDENTITY-01`

Parent final-ledger commit: `98bc69b87c66212e92dc2efc814bbffc4cf847dd`

Parent public CI: Lean Action run `29977016712`, build job `89110861524`, passed in `1m55s`.

## Governing objective

RH remains the target. A historical route is tested at the level of its actual mechanism, not
closed after one summary or one finite lemma. Original conjectures and direct RH attacks remain
open, but the present selection favors a source edge that can discriminate a near-proof from a
normalization or sign illusion.

## Cross-route comparison

| candidate | exact next object | discriminating value | verdict |
| --- | --- | --- | --- |
| H7 archimedean tail density | Derive the actual sine-cosine source samples and diagonal derivative, identify the finite matrix density as a positive rank-two Cauchy sum, and integrate it conditionally under an explicit `h_+` sign premise. | Pole and prime blocks already inhabit the same divided-difference API. This is the last actual source block before a three-block assembly can be audited. A factor, diagonal, or sign mismatch would directly damage the 2026 spectral program. | **Selected.** |
| H1 inverse Mellin and contour | Prove vertical integrability of the regularized `G_t`, construct `g_t`, prove support/boundedness, Mellin convolution, and move the contour. | Directly advances the individual-zero obstruction, but support, decay, inversion, and contour transport form a coupled analytic package too broad for one bounded endpoint. | `OPEN / HIGH_VALUE`. |
| H7 true ground-state/prolate comparison | Prove the Rayleigh-excess/spectral-gap ratio tends to zero for actual source matrices. | This is closer to the RH-bearing limit, but no declaration yet assembles the actual archimedean block, so the ratio would still be abstract or incomplete. | `OPEN / AFTER_SOURCE_ASSEMBLY`. |
| H9 actual Conrey flat-prefix exclusion | Exclude `B_m=0, A_m=H` for every relevant quadratic-character prefix. | Historically distinct, but the previous source audit found no bounded theorem mechanism beyond finite navigation scans. | `OPEN / REVISIT_ON_NEW_INPUT`. |
| H10/H11 regularized trace or sparse-exception amplification | Supply a number-field distributional trace with uniform tails, or prove one off-line zeta orbit creates non-sparse statistical excess. | High endpoint value, but neither route currently has a source-exact intermediate narrower than its central open problem. | `OPEN`. |

This choice alternates back from H1 and completes an actual-source triad; it is not a numerical
constant campaign. After this bounded archimedean endpoint, the portfolio must rerank across
families rather than assume H7 remains selected.

## Locked source mechanism

Primary source: Groskin, [arXiv:2607.02828](https://arxiv.org/abs/2607.02828), equation
`arch-source` and Theorem 3.2. For `L=log c`, `rho=2*pi/L`,

```text
h_+(r) = Re digamma(1/4+i*r/2) - log pi,

S(r,x,L) = integral_0^L sin(2*pi*x*(1-y/L))*cos(r*y) dy.
```

The derivative of the finite-cutoff archimedean source at positive `T` is

```text
(1/pi^2) h_+(T) S(T,x,L).
```

At an integer node `n`, with `a=T/rho` and `T>rho*N`, the source claims

```text
S(T,n,L) = (2*sin(L*T/2)^2/rho) * n/(a^2-n^2),

partial_x S(T,x,L)|_(x=n)
  = (2*sin(L*T/2)^2/rho) * (a^2+n^2)/(a^2-n^2)^2.
```

Consequently the divided-difference matrix density is

```text
h_+(T)*sin(L*T/2)^2/(pi^2*rho) * (p_T*p_T^t + q_T*q_T^t),
p_T(n)=1/(a-n), q_T(n)=1/(a+n).
```

## Decision

Select node `H7-WEIL-ARCHIMEDEAN-TAIL-DENSITY-01` and preregister campaign
`LITERATURE-20260723-H7-WEIL-ARCHIMEDEAN-TAIL-DENSITY-01`.

The fixed endpoint starts from the literal interval integral `S`, proves both node and derivative
formulas, constructs the corresponding actual tail-density divided-difference matrix, proves its
rank-two Cauchy decomposition and quadratic sum-of-squares identity, and proves nonnegativity of
the integrated increment only under an explicit pointwise premise `0<=h_+(r)`.

The campaign does not prove `h_+(r)>0` for `r>=7`, strict positive definiteness of a nontrivial
interval increment, strict total positivity of all minors, the infinite tail limit, a tail budget,
the total pole/prime/archimedean sign, Herglotz, simple-even ground states, source convergence, H7,
or RH.

## Local selected-node result

The selected node reaches its full registered endpoint locally. Lean differentiates the literal
interval kernel under the integral, proves both source formulas, constructs the actual finite
matrix, and derives the exact positive-sign Cauchy rank-two density. The diagonal falsification
guard passed with no normalization mismatch.

The entrywise interval increment has the claimed quadratic integral identity and is positive
semidefinite under the explicit interval premise `0<=h_+`. Continuity of the literal digamma
density is proved from Gamma analyticity and nonvanishing, not assumed. The 973-line module, 12
exact checks, 11 standard-only axiom prints, empty scan, and 8,756-job build pass locally.

This adds one actual source block and does not change the RH frontier. Frozen implementation
commit `9546806d8c3d0afeef9f6c7ee674982e8710576a` passed public Lean Action run `29979643215`,
build job `89118608592`, in `2m32s`. Immutable-evidence commit
`213af9d7a26a23a828b12e5b7523d520c424b1b4` passed run `29979851450`, build job `89119211639`,
in `1m56s`. Only final-ledger CI remains before successor reranking.
