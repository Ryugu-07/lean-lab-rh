# H1 Hardy--Littlewood Finite Mean-Square Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Node: `H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `PUBLIC_IMPLEMENTATION_GREEN / IMMUTABLE_EVIDENCE_CI_PENDING`

## Parent and route selection

- `parent_closure`: Hardy--Littlewood source-normalization receipt
  `4ba4cdf4cdefde88b483e03d4871abf63d6e4020`, Lean Action run `30469848450`, build job
  `90636930282`.
- `selected_node`: `H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`.
- `selection_reason`: fresh comparison with H2, H7/H8, H10, H11, H12, and H14 leaves those
  routes at broad global producers, while the 1921 Hardy--Littlewood source has both a compiled
  normalization/finite-count consumer and one precise unformalized finite Dirichlet-polynomial
  hinge in Lemmas 6--8.
- `material_difference`: this is not a numerical-constant optimization and does not continue H1
  merely because H1 was last active. It tests whether the source's stronger
  `O(N / log N)` off-diagonal estimate can be weakened to the `O(N)` statement actually
  sufficient for its finite mean-square conclusion.
- `historical_omission_question`: did the stronger Lemma 6 asymptotic obscure a simpler finite
  premise that is enough for the zero-count mechanism?

## Source lock

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), pp. 286--288, Lemmas 4--8, especially equations
  `(2.32)`, `(2.41)`, and `(2.42)`:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

The source defines

```text
Theta(s) = sum_(n>=2) (-1)^(n-1) n^(-s) / log n
psi(t)   = Theta(1/2+i*t)
```

and proves the uniform interval estimate

```text
integral_[T,2T] |psi(t+u)|^2 dt = O(T),  0 <= u <= T.
```

Its finite expansion uses the off-diagonal kernel

```text
1 / (sqrt(m*n) * log(m) * log(n) * |log(m/n)|).
```

Hardy--Littlewood prove the stronger sum `O(N / log N)`. This campaign fixes only the finite
polynomial conclusion and asks Lean to verify that a universal `O(N)` kernel bound already
suffices.

## Exact mathematical statement

For `n >= 2`, put

```text
a_n = (-1)^(n-1) / (sqrt(n) * log(n)),
P_N(t) = sum_(2 <= n <= N) a_n * exp(-i*t*log(n)).
```

Prove that there is a universal real constant `C > 0` such that for every natural `N`, every
real `A`, every real shift `u`, and every `L >= 0`,

```text
integral_[A,A+L] |P_N(t+u)|^2 dt <= C * (L + N).
```

Consequently, when `(N : R) <= L`,

```text
integral_[A,A+L] |P_N(t+u)|^2 dt <= 2*C*L.
```

The proof must include a universal linear bound for the finite off-diagonal kernel sum. It may
choose any explicit witness constant; optimizing that witness is outside the campaign.

## Proposed Lean endpoint

Create `LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean` only after this docs-only
preregistration passes public CI.

Names may be adjusted to local style, but the endpoint may not be weakened silently.

1. Define the nonnegative diagonal coefficient
   `hardyLittlewoodLogSquareCoeff n`, equal to `1 / (n*log(n)^2)` for `n >= 2`.
2. Prove its summability and an explicit bound independent of the truncation length.
3. Define the finite Hardy--Littlewood coefficient and polynomial with the literal alternating
   sign and logarithmic frequency.
4. Define the off-diagonal logarithmic kernel on distinct indices `m,n >= 2`.
5. Prove an explicit universal `Coff > 0` for which the double kernel sum over
   `2 <= m,n <= N`, `m != n`, is at most `Coff*N`.
6. Prove the exact finite norm-square expansion and the complex exponential interval-integral
   formula, including the nonzero-frequency bound `<= 2/|log(m/n)|`.
7. Deduce the universal shifted finite mean-square theorem stated above.
8. Deduce its `N <= L` corollary.
9. Compile an aggregate endpoint certificate.

Register one proven Target and exact TargetChecks. Add selected standard-only axiom prints to
`AxiomsAudit.lean`. Import the module from `LeanLab.lean`.

## Intended proof decomposition

```text
1/(n*log(n)^2)
  <= 6*(1/log(n) - 1/log(n+1))
-> bounded diagonal sum
-> exact finite norm-square double expansion
-> diagonal contribution <= Cdiag*L
-> write the upper triangle as m=n+r
-> r<=n: 1/log(1+r/n) <= O(n/r), then use harmonic(n)<=1+log(n)
-> r>n: log(1+r/n)>=log(2), then use Cauchy--Schwarz plus the diagonal sum
-> off-diagonal contribution <= Coff*N
-> shifted finite mean square <= C*(L+N).
```

The first telescope inequality and the resulting infinite diagonal bound were compiled in a
temporary no-sorry feasibility probe before preregistration. They are now production theorems
in `LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean`; downstream use remains subject to
the mechanical and public-CI gates below.

## Success, partial, falsification, and obstruction criteria

`FULL_SUCCESS` requires all nine endpoint items, no placeholders, warning-as-error compiles,
exact TargetChecks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, a full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the bounded diagonal theorem, exact finite norm-square expansion,
and a compiled reduction of the full finite mean-square endpoint to one named logarithmic
off-diagonal inequality. A generic finite-sum helper alone is not meaningful partial progress.

`WEAKENING_FALSIFIED` requires a compiled family or inequality showing that the proposed linear
off-diagonal bound is false. This would force restoration of a stronger source estimate or a
different finite decomposition.

`BLOCKED_ANALYTIC` requires the exact first unproved real-logarithmic or interval-integral
statement after all preceding pieces compile. The obstruction must be recorded in `attempts/`
and `research/hard_gap_dag.md`.

## Negative controls and claim boundary

- The campaign does not identify the infinite conditionally convergent series with
  `hardyLittlewoodEtaPrimitive`.
- It does not prove Hardy--Littlewood Lemma 4's uniform truncation error.
- A finite-polynomial bound uniform in `N <= L` cannot be applied to the infinite source series
  without that truncation theorem.
- It does not prove the second mean-square estimate for the actual source coordinate `X`.
- It does not instantiate the asymptotic parameter budget in
  `hardyLittlewood_source_finite_count`.
- Success is a source finite-mean-square producer and a premise minimization, not an
  unconditional linear zero count, positive proportion, H1, or RH.

## Successor obstacle map

- `OBS-H1-HARDY-LITTLEWOOD-ETA-TRUNCATION-01`: formalize Lemmas 3--4 with uniform error when
  `|t| <= A*N`; this is the first infinite-series bridge after the present finite endpoint.
- `OBS-H1-HARDY-LITTLEWOOD-ETA-SERIES-IDENTIFICATION-01`: identify the eta primitive with the
  relevant component of `Theta(1/2+i*t)`.
- `OBS-H1-HARDY-LITTLEWOOD-ETA-ERROR-MEAN-SQUARE-01`: combine truncation, finite mean square,
  and primitive identification.
- `OBS-H1-HARDY-LITTLEWOOD-X-MEAN-SQUARE-01`: prove Lemma 11 for the actual source coordinate.
- `OBS-H1-HARDY-LITTLEWOOD-PARAMETER-BUDGET-01`: choose the uniform count parameters.

## Audit gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. exact checks for every registered theorem;
4. selected `#print axioms` output contains only accepted standard foundations;
5. warning-as-error compile of the new module and registration files;
6. full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop only this local campaign and rerank the
historical routes. The persistent RH Goal remains active.
