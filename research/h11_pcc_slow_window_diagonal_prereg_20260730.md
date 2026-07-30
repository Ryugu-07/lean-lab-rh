# H11 PCC Slow-Window Diagonal Preregistration

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H11-PCC-SLOW-WINDOW-DIAGONAL-01`

Selected node:
`H11-GOLDSTON-PCC-SLOW-WINDOW-DIAGONAL-01`

Mode: `LITERATURE / OMISSION-AUDIT / FALSIFICATION`

Status: `PREREGISTRATION_PUBLIC_GREEN / IMPLEMENTATION_PUBLIC_GREEN`

Preregistration public receipt:

- commit: `3ab1ad271ccd4ea61b99097774d2607fb777b5df`;
- Lean Action run: `30519421563`;
- build job: `90796328588`;
- duration: `2m3s`;
- result: pass.

## Primary-source anchor

Goldston--Lee--Schettler--Suriajaya,
*Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I: Simple and Critical
Zeros*, arXiv:2503.15449v4:

- the PCC statement is uniform on every fixed interval
  `0<lambda0<=lambda<=lambda1<infinity`;
- Remark 1 after PCC says `lambda0` and `lambda1` may be taken as functions of `T` with
  `lambda0(T)->0` and `lambda1(T)->infinity`;
- Section 8 uses this slow choice together with `lambda^2<=L` to derive HMH.

Source:
`https://arxiv.org/abs/2503.15449v4`.

The moving-parameter conclusion is a diagonal consequence, not literal substitution into
fixed-parameter convergence.

## Fixed endpoint

For an error family `e : Nat -> Nat -> Real` and a growth cap `cap : Nat -> Nat`, prove:

1. if `cap -> infinity` and, for every fixed positive stage `k`,
   `e(n,k) -> 0`, then there exists a positive stage function `stage(n)`;
2. `stage -> infinity`;
3. eventually `stage(n)<=cap(n)`;
4. `e(n,stage(n))->0`;
5. the associated lower window `1/stage(n)` tends to zero and upper window `stage(n)` tends to
   infinity;
6. therefore a cap such as `floor(sqrt(L(n)))` can be retained whenever that cap tends to
   infinity.

The theorem may use absolute values or norms in its error hypothesis. It may return the stage
function existentially rather than define a canonical one.

## Negative control

Compile an explicit error array with:

- `e(n,k)->0` for every fixed `k`;
- the fast diagonal `k=n+1` has error identically one.

Thus no theorem may quantify over every moving stage tending to infinity.

## Success boundary

Full local success requires the positive diagonal theorem, reciprocal-window limits, cap
preservation, and the fast-diagonal counterexample, together with registration, exact checks,
standard-only axiom audit, empty forbidden scans, full build, and public evidence.

A theorem assuming the moving-window error already tends to zero is circular infrastructure and
does not meet the endpoint.

Expected classification:

- `result=PCC_SLOW_WINDOW_DIAGONAL_JUSTIFIED`;
- `historical_route_coverage_delta=1`;
- `source_quantifier_bridge_delta=1`;
- `pcc_delta=0`;
- `hmh_delta=0`;
- `sparse_exception_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No `LeanLab/` or theorem-registration file may be created or edited before this docs-only
preregistration passes public Lean Action CI.
