# H1 Hardy--Littlewood Linear Count Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01`

Node: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`

Classification: `FULL_SUCCESS / FINITE_EXCEPTIONAL_SET_COUNT_BRIDGE_FORMALIZED`

Public state: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_PENDING`

## Compiled result

The 867-line no-sorry module
`LeanLab/Riemann/HardyLittlewoodLinearCount.lean` proves:

1. continuity of the moving integrals
   `I(t,H)=integral_[t,t+H] X` and
   `absI(t,H)=integral_[t,t+H] |X|`;
2. strict and non-strict square-threshold Markov inequalities in denominator-free `ENNReal`
   form;
3. the two source-shaped exceptional-set bounds and their union bound;
4. the strict triangle gap `|I(t,H)|<absI(t,H)` outside the two bad sets;
5. pairwise disjointness and exact length-`H` measure of the first blocks;
6. preservation of that measure under restriction to `[T,2T]` when `2*n*H<=T`;
7. the charge
   `failed.card * H <= measure bad`;
8. the natural lower bound `n-b<=good.card` when the bad-set budget is at most `b*H`;
9. one actual nontrivial critical-line zeta zero in every good pair block, with injective
   selected ordinates;
10. a fixed positive-half finite corollary;
11. a null-set countermodel containing every finitely sampled left endpoint.

The aggregate theorem is:

```text
hardyLittlewood_source_finite_count
```

It starts from the two source second-moment hypotheses, the absolute-integral lower estimate on
`[T,2T]`, an exact zero-coordinate adapter, and an explicit finite `ENNReal` budget. It returns
both the natural count lower bound and injective witnesses for actual critical-line zeta zeros.

## Proof mechanism

Set `theta=A*H/2`. Markov's inequality applied to `|psi|^2` and `|I|^2` bounds

```text
U = {t | theta < |psi t|}
V = {t | theta <= |I(t,H)|}.
```

Outside `U union V`, the source lower estimate

```text
A*H - |psi t| <= absI(t,H)
```

gives `theta<=absI(t,H)` while `|I(t,H)|<theta`. The strict integral triangle gap forces both
signs and hence a zero in `(t,t+H)`.

For each adjacent pair, failure means that its entire first `Ico` block lies in the bad set.
Those first blocks are disjoint and each has restricted measure exactly `H`, so every failed
pair consumes one full unit of measure `H`. The remaining open pair blocks are disjoint, making
the selected zero ordinates injective.

## Premise minimization

The final generic consumer asks for the lower estimate only inside its finitely many first
blocks. The source-shaped theorem asks for it only on `[T,2T]`. An earlier local draft used an
unnecessary all-real quantifier; it was removed before the frozen implementation.

This matters for the next producer campaign: formalizing Hardy--Littlewood's eta estimate does
not need to establish a global statement that the source never uses.

## Negative control

`hardyLittlewoodEndpointSet_volume_zero` proves that the finite set of all sampled left
endpoints has Lebesgue measure zero while containing every sample. Therefore no endpoint-grid
test can replace the source's whole-first-interval inclusion argument.

## Audit

- production proof: 867 lines;
- exact TargetChecks: six;
- selected axiom prints: nine, each only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, custom axiom, `native_decide`, `opaque`, or `unsafe`;
- no heartbeat, recursion-depth, or resource relaxation;
- warning-as-error checks: module, Targets, TargetChecks, AxiomsAudit, and root pass;
- full project build: `8798/8798`;
- three forbidden scans and `git diff --check`: empty;
- frozen five-file proof and registration diff: empty after implementation publication;
- inherited protected files remain unstaged.

## Claim boundary

This formalizes the finite measure-to-count inference in Hardy--Littlewood 1921, equations
`(2.82)`--`(2.87)` and section `2.9`.

It does not yet prove:

- the source-normalized real Hardy `X/Z` coordinate package;
- the eta lower estimate and its error second moment;
- the source moving-integral second moment;
- the asymptotic parameter budget for arbitrarily large `T`;
- an unconditional linear count, positive proportion, H1, or RH.

Deltas: historical route coverage `+1`, source logic `+1`, hard gap `0`, RH frontier `0`.

The persistent RH Goal remains active.

## Public chain

- Preregistration commit `d36f9d0c8005691e9043165c062bf60a9e311722` passed Lean Action
  run `30438867401`, build job `90533061533`, in `1m57s`.
- Frozen implementation commit `8f3742c62a381293fa201358cf58130d2c333c48` passed Lean Action
  run `30464674314`, build job `90619318156`, in `2m52s`.
- Immutable-evidence commit `9f161104ed086a137e221b6c8ffe3d3bdda65005` passed Lean Action
  run `30465073931`, build job `90620648692`, in `2m14s`.
- Final-ledger commit `25316ea1b408731da6581a371afcaccd2bf169f7` passed Lean Action
  run `30465345680`, build job `90621575136`, in `1m41s`.

The closure receipt records this chain and closes only the fixed finite count bridge.
