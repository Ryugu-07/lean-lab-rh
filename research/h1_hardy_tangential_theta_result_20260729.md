# H1 Hardy Tangential Theta Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-TANGENTIAL-THETA-01`

Node: `H1-HARDY-TANGENTIAL-THETA-LIMIT-01`

Classification: `FULL_SUCCESS / HARDY_1914_UNCONDITIONAL_INFINITY_FORMALIZED`

Public state: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_PENDING`

## Compiled result

The new no-sorry modules `LeanLab/Riemann/HardyTangentialTheta.lean` and
`LeanLab/Riemann/HardyTangentialThetaIntegral.lean`, totaling 2,489 lines, prove:

1. Hardy's exact theta parameter and its translation from the cusp `-1` to `0`;
2. a principal-branch Jacobi-theta inversion to a half-integer theta series;
3. the exact real tangential geometry, including `Im (-1/(tau+1)) -> +infinity`;
4. Gaussian decay after every fixed polynomial loss for every iterated theta derivative;
5. all-order flatness of `hardyThetaBoundaryTerm` at `alpha -> pi/2` from below;
6. all-order differentiation under Hardy's actual Xi integral throughout the open strip;
7. identification of order `2*p` with the literal real Abel moment;
8. equation (3) with sign `(-1)^p` and denominator `4^(2*p)`;
9. `hardyXiAbelMomentLaw_unconditional : HardyXiAbelMomentLaw`;
10. `infinite_criticalLineZeros_hardy`, giving infinitely many actual nontrivial zeros on the
    critical line.

## Proof mechanism

For `tau(alpha)=I*exp(I*alpha)`, set `sigma=tau+1` and `tau'=-1/sigma`. Translation and
Mathlib's branch-explicit Jacobi theta functional equation rewrite Hardy's boundary term as a
principal square-root prefactor times a half-integer theta series at `tau'`. Along the real
source path, `Re(tau')=-1/2` and `Im(tau')` tends to positive infinity.

A Cauchy estimate on the disk of radius `Im(tau')/2` converts the explicit half-integer Gaussian
bound into rapid decay for every complex derivative. The multiplier is differentiated only
after proving that its argument stays in the slit plane. The identities

```text
u' = -I*u*(1+u)
prefactor' = prefactor*(-I/4-(I/2)*u)
```

close a finite six-term basis under differentiation. A recursive finite model is proved equal
to every actual iterated derivative, and every basis term tends to zero.

On the integral side, spare strip width supplies a locally uniform majorant for every next
alpha derivative. At even order the explicit kernel is exactly Hardy's real source moment.
Equation (2) rearranges to

```text
hardyXiInteriorIntegral alpha + hardyThetaBoundaryTerm alpha
  = pi * cos(alpha/4).
```

Taking `2*p` derivatives and then the left Abel limit gives the source constant. No endpoint
Lebesgue integral is introduced.

## Omission reading

Hardy's short note invokes a general Bohr--Riesz summability result at the decisive cusp and
does not expose the branch, derivative, or domination bookkeeping. The formal proof replaces
that invocation by a concrete Jacobi-theta transformation plus all-order Cauchy/Gaussian
estimates. This closes the omitted analytic bridge while preserving Hardy's normalization and
one-sided filter.

## Audit

- production proof: 2,489 lines across two modules;
- exact TargetChecks: four;
- selected axiom prints: six, each only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, custom axiom, `native_decide`, `opaque`, or `unsafe`;
- no heartbeat, recursion-depth, or resource relaxation;
- warning-as-error checks: both modules, Targets, TargetChecks, AxiomsAudit, and root pass;
- full project build: `8797/8797`;
- frozen six-file proof and registration diff: empty through the final ledger;
- inherited protected files remain untouched and unstaged.

## Claim boundary

This formalizes Hardy's qualitative theorem that infinitely many nontrivial zeta zeros lie on
the critical line. It does not prove a quantitative lower bound for their count, a positive
proportion of all zeros, H1, or RH.

Deltas: historical route coverage `+1`, source logic `+1`, hard gap `0`, RH frontier `0`.

The persistent RH Goal remains active.

## Public chain

- Preregistration commit `648d8e8140f1af0ea5726cf030b8ab4bc4dc8581` passed Lean Action
  run `30429533400`, build job `90503309053`, in `2m43s`.
- Frozen implementation commit `75f5c575b2c3f050f0e5703efb5ce6851d97775c` passed Lean Action
  run `30435633763`, build job `90522592740`, in `2m17s`.
- Immutable-evidence commit `85f0ae62feb457961a3e71ca15db50fa195ce459` passed Lean Action
  run `30436167642`, build job `90524303908`, in `2m7s`.
- Final-ledger commit `2365765bf5ec9eb155312dce119fe6cccbbbff56` passed Lean Action
  run `30436418445`, build job `90525116015`, in `1m44s`.

The closure receipt records this chain and closes only the fixed node.
