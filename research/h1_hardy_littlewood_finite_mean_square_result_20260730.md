# H1 Hardy--Littlewood Finite Mean-Square Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Node: `H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Classification: `FULL_SUCCESS / FINITE_MEAN_SQUARE_FORMALIZED`

Public state: `LOCAL_AUDIT_GREEN / PUBLIC_IMPLEMENTATION_CI_PENDING`

## Compiled result

The 1171-line no-sorry module
`LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean` proves:

1. summability of `1/(n*log(n)^2)` with the explicit bound `6/log(2)`;
2. the literal alternating Hardy--Littlewood coefficient and shifted finite polynomial;
3. exact coefficient norms and the finite norm-square double expansion;
4. a near-diagonal harmonic bound and a far-diagonal Cauchy bound;
5. a universal `O(N)` upper-triangular logarithmic-kernel estimate;
6. the exact nonzero-frequency cosine integral bound, uniform in the phase shift;
7. the shifted finite mean square `O(L+N)`;
8. the uniform `O(L)` corollary whenever `(N : R)<=L`.

The aggregate theorem is:

```text
hardyLittlewoodFiniteMeanSquare_endpoint
```

## Omission result

Hardy--Littlewood's Lemma 6 proves the stronger off-diagonal estimate `O(N/log N)`.
The compiled proof shows that the finite Lemma 7/8 mean-square conclusion uses only a universal
linear estimate. The proof splits `m=n+r`: for `r<=n`, a logarithmic lower bound reduces to a
harmonic sum; for `r>n`, `log(1+r/n)>=log 2` and Cauchy--Schwarz reduce the contribution to the
bounded diagonal coefficient sum.

This is a premise minimization, not a numerical-constant optimization.

## Claim boundary

The result concerns finite Dirichlet polynomials only. It does not prove:

- the uniform conditional-series truncation in source Lemmas 3--4;
- identification of the eta primitive with the source series;
- the eta truncation-error second moment;
- the actual source-coordinate moving-integral moment of Lemma 11;
- the count parameter budget;
- an unconditional linear critical-zero count, H1, or RH.

The first successor obstacle is
`OBS-H1-HARDY-LITTLEWOOD-ETA-TRUNCATION-01`.

The persistent RH Goal remains active.

## Local audit

- production proof: 1171 lines;
- exact TargetChecks: six;
- selected axiom prints: six, each only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, custom axiom, `native_decide`, `opaque`, or `unsafe`;
- no heartbeat, recursion-depth, or resource relaxation;
- warning-as-error checks: module, Targets, TargetChecks, AxiomsAudit, and root pass;
- full project build: `8800/8800`;
- forbidden/resource scans and `git diff --check`: empty;
- inherited protected files remain unstaged.
