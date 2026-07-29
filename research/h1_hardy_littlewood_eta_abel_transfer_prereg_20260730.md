# H1 Hardy--Littlewood Eta-to-Theta Abel Transfer Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `FULL_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_CI_PENDING`

## Parent and route selection

- `parent_closure`: finite mean-square receipt
  `5ad0b8b5795820dee3766c6ca2dd816bb41acdb1`, Lean Action run `30476269858`, build job
  `90658643380`.
- `selected_node`: `H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`.
- `selection_reason`: H2, H7/H8, H10, H11, H12, and H14 remain at broad global producers,
  while Hardy--Littlewood Lemma 4 is one exact, bounded source inference between the open eta
  remainder and the compiled finite Theta-polynomial mean square.
- `material_difference`: this campaign studies conditional convergence and summation by parts.
  It neither optimizes the finite kernel constant nor treats H1 adjacency as sufficient.
- `historical_omission_question`: does Lemma 4 require a new oscillatory estimate, or is it a
  lossless formal consequence of Lemma 3 after the reciprocal-log Abel transform?

## Source lock

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), pp. 286--287, Lemmas 3--4:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

For `s=sigma+i*t`, Lemma 3 supplies

```text
eta(s) = sum_(n<=x) (-1)^(n-1)*n^(-s) + O(x^(-sigma))
```

uniformly for `sigma>=sigma0>0` and `|t|<A*x`. If `X=floor(x)`, Lemma 4 uses

```text
sum_(n=X+1)^infinity (-1)^(n-1)*n^(-s)/log(n)
  = sum_(n=X+1)^infinity
      (1/log(n)-1/log(n+1))
      * sum_(m=X+1)^n (-1)^(m-1)*m^(-s).
```

The block sum is the difference of two eta remainders. The reciprocal-log differences are
nonnegative and telescope. Thus Lemma 4 introduces no independent zeta estimate once Lemma 3
is available.

## Exact mathematical statement

Let

```text
a_s(n) = (-1)^(n-1)*n^(-s),
E_N(s) = sum_(1<=n<=N) a_s(n),
Q_N(s) = sum_(2<=n<=N) a_s(n)/log(n).
```

Fix `sigma>0`, `K>=0`, `N0>=2`, `s`, and an eta value `etaValue`. Assume

```text
forall N>=N0,
  norm(etaValue-E_N(s)) <= K*(N:Real)^(-sigma).
```

Prove that there is a complex `thetaValue` such that

```text
Tendsto (fun N => Q_N(s)) atTop (nhds thetaValue)
```

and there is one explicit universal constant `C>0` such that, for every `N>=N0`,

```text
norm(thetaValue-Q_N(s)) <= C*K*(N:Real)^(-sigma).
```

The preferred witness is `C=2`; a larger explicit universal constant is allowed only if the
proof records where it enters. Constant optimization is outside the campaign.

The theorem must be stated so that a single eta remainder constant uniform over a parameter
region transfers to a single Theta remainder constant over the same region.

## Proposed Lean endpoint

Create `LeanLab/Riemann/HardyLittlewoodEtaAbelTransfer.lean` only after this docs-only
preregistration passes public CI.

Names may be adjusted to local style, but the endpoint may not be weakened silently.

1. Define the literal source alternating Dirichlet term, eta partial sum, reciprocal-log
   weight, and Theta partial sum.
2. Prove an exact complex finite Abel identity for a shifted block.
3. Prove positivity and telescoping of
   `1/log(n)-1/log(n+1)` on the source range.
4. Prove that if every partial block after `N` has norm at most `B`, then every
   reciprocal-log weighted block after `N` has norm at most `B/log(N+1)`, hence at most `B`.
5. Convert the eta remainder hypothesis into the partial-block bound
   `2*K*N^(-sigma)`.
6. Prove that the Theta partial sums are Cauchy and therefore converge in `Complex`.
7. Pass the finite block estimate to the limit and obtain the uniform
   `C*K*N^(-sigma)` truncation theorem.
8. Compile an aggregate endpoint certificate.
9. Register one proven Target and exact TargetChecks. Add selected standard-only axiom prints
   to `AxiomsAudit.lean`. Import the module from `LeanLab.lean`.

Existing infrastructure that may be reused:

- `Finset.sum_Ico_by_parts` in Mathlib;
- `orderedDirichletPartialSum` and `OrderedDirichletHasSum` in
  `LeanLab/Riemann/ChebyshevMellin.lean`;
- logarithmic coefficient bounds in
  `LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean`.

## Intended proof decomposition

```text
eta remainder at n and N
-> norm(E_n-E_N) <= K*n^(-sigma)+K*N^(-sigma)
-> norm(E_n-E_N) <= 2*K*N^(-sigma), since sigma>0 and n>=N
-> finite Abel identity with w_n=1/log(n)
-> positive telescoping differences
-> weighted block <= 2*K*N^(-sigma)/log(N+1)
-> weighted partial sums are Cauchy because N^(-sigma) -> 0
-> Complex completeness gives thetaValue
-> closed norm bound passes to the limit
-> ordered Theta remainder O(N^(-sigma)).
```

## Success, partial, falsification, and obstruction criteria

`FULL_SUCCESS` requires all nine endpoint items, no placeholders, warning-as-error compiles,
exact TargetChecks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, a full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the exact shifted finite Abel identity, the bounded-block
weighted estimate, and a compiled reduction of ordered Theta convergence to the stated eta
remainder hypothesis. A generic summation-by-parts identity alone is not meaningful partial
progress.

`TRANSFER_FALSIFIED` requires a compiled counterexample to the stated eta-to-Theta implication.
An index or endpoint error that invalidates `C=2` but leaves another universal `C` valid is a
repair, not falsification.

`BLOCKED_FORMAL` requires the exact first unproved finite Abel, monotonicity, Cauchy, or
limit-passage statement after all preceding pieces compile. The obstruction must be recorded
in `attempts/` and `research/hard_gap_dag.md`.

## Negative controls and claim boundary

- The eta remainder hypothesis is not proved in this campaign.
- `orderedAlternatingDirichletHasSum` supplies qualitative ordered convergence for a related
  sign convention; it does not supply Hardy--Littlewood's uniform `O(N^(-sigma))` remainder.
- A crude derivative or Dirichlet-test estimate carrying `1+|s|` is not sufficient for the
  source region `|t|<A*N`.
- The resulting `thetaValue` is an ordered-series value. It is not identified here with
  `hardyLittlewoodEtaPrimitive` or any integral primitive.
- The campaign proves no infinite-series mean square, source-X moment, count parameter budget,
  unconditional linear count, positive proportion, H1, or RH.

## Successor obstacle map

- `OBS-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`: formalize the actual Lemma 3
  `O(N^(-sigma))` remainder uniformly for `sigma>=sigma0>0`, `|t|<A*N`.
- `OBS-H1-HARDY-LITTLEWOOD-ETA-SERIES-IDENTIFICATION-01`: identify the ordered Theta value at
  the critical line with the source primitive used in the count route.
- `OBS-H1-HARDY-LITTLEWOOD-ETA-ERROR-MEAN-SQUARE-01`: combine the transfer, finite mean square,
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
receipt through separate public-green commits. Then stop only this local campaign and rerank
the historical routes. The persistent RH Goal remains active.

## Local result

All nine endpoint items compile in the 488-line no-sorry module
`LeanLab/Riemann/HardyLittlewoodEtaAbelTransfer.lean`. The explicit transfer constant is
`2/log 2`. The arbitrary-parameter-family theorem confirms that one eta remainder constant
uniform on a source region gives one Theta remainder constant on the same region.

The historical omission test succeeds: Lemma 4 contains no independent oscillatory estimate;
the first remaining analytic producer is the actual Lemma 3 eta remainder. Full local audit
passes `8801/8801`.

Frozen implementation commit `f03c6a8f5d35945d34407d0627b7a5f4f629cb9e` passed independent
Lean Action run `30479693865`, build job `90670228283`, in `2m17s`. The five proof and
registration files are now frozen. Immutable-evidence CI, final-ledger CI, and closure-receipt
CI remain required.
