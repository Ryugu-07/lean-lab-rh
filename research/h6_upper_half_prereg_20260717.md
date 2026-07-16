# H6 de Bruijn Upper-Half Preregistration

Date: 2026-07-17

Campaign: `CAMPAIGN-20260717-H6-UPPER-HALF-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION_LOCAL_READY_PUBLIC_CI_PENDING`

## Route selection

H6-B, H6-H1, H6-H2a, H6-H2b, and H6-H2c are publicly complete. In particular, the exact
source-normalized heat family is entire of order at most one, its time-zero zeros lie in the
strict strip `-1 < Im(z) < 1`, the all-real-zero time set is closed, and real-zero times are
forward preserved. The remaining H6 threshold frontier begins with proving that this set is
nonempty.

Fresh value-ranked selection compares the following open directions.

- Direct H6-E/G8, W2/G7, and M2/G3 attacks remain permitted, but the current obstruction map has
  no new unconditional positivity or approximation mechanism after the compiled audits.
- The Polymath `Lambda <= 0.22` theorem would prove a stronger numerical upper bound, but requires
  extensive effective saddle-point, interval-arithmetic, and global nonvanishing infrastructure.
- De Bruijn's classical `t = 1/2` theorem uses exactly the strip coordinate, order-one
  factorization, vertical averages, `cosh` heat limit, and Jensen persistence now compiled by the
  preceding H6 campaigns. It proves the first concrete good time and closes threshold
  nonemptiness without numerical premises.

Select the exact de Bruijn strip-contraction theorem and its `t=1/2` endpoint. A finite-degree
polynomial theorem, a conditional theorem, or a theorem assuming a nonempty good-time set does
not close this campaign.

## Exact mathematical endpoint

For every `0 <= t <= 1/2`, every zero of the exact source-normalized `H_t` lies in the contracted
closed strip

`Im(z)^2 <= 1 - 2*t`.

Consequently every zero of `H_(1/2)` is real:

`deBruijnNewmanAllZerosReal (1/2)`.

The quantitative strip theorem and the endpoint are both required. The endpoint proves a
concrete member of the good-time set; it does not prove that time zero is good.

## Fixed Lean endpoints

The final declarations must have at least the following strength:

```lean
theorem deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
    {t : Real} (ht0 : 0 <= t) (hthalf : t <= (1 : Real) / 2)
    {z : Complex} (hz : deBruijnNewmanH t z = 0) :
    z.im ^ 2 <= 1 - 2 * t

theorem deBruijnNewmanAllZerosReal_one_half :
    deBruijnNewmanAllZerosReal ((1 : Real) / 2)
```

Binder order or theorem names may change, but the exact source family, the full interval, the
quadratic strip width, and the unconditional half-time endpoint may not be weakened.

## Fixed proof architecture

1. Prove conjugation symmetry for `H_t`, the finite `cosh` approximants, and their vertical
   averages. Retain the existing evenness, source positivity at spatial zero, and order-one
   bounds.
2. For a real entire order-one function with all zeros in `Im(r)^2 <= muSq`, pair every genus-one
   Weierstrass factor at `r` with the factor at `conj(r)`. Prove, for `a>0`, `Im(z)>0`, and
   `muSq-a^2 < Im(z)^2`, that the paired lower-shift norm is strictly smaller than the paired
   upper-shift norm. The polynomial core is the exact identity behind de Bruijn's shifted Jensen
   theorem; exponential norms cancel because `1/r + 1/conj(r)` is real.
3. Construct the conjugation involution on the multiplicity-bearing Hadamard divisor index.
   Prove that conjugation preserves analytic zero order; fixed real roots and nonreal conjugate
   pairs must both be handled without selecting simple zeros.
4. Reindex the infinite product along that involution and deduce the entire-function vertical
   average contraction

   `zeros(F) subset {Im^2 <= muSq}`

   implies

   `zeros(verticalAverage a F) subset {Im^2 <= muSq-a^2}`

   whenever `0 <= a^2 <= muSq`. Empty divisors, possible real fixed points, and zero factors are
   separate cases.
5. Start from the compiled strict time-zero strip, weakened only to `Im(z)^2 <= 1`. For each
   positive natural `n`, iterate the average `n` times with
   `a_n = sqrt(2*t/n)`. Inductively subtract `a_n^2` from the squared half-width, obtaining
   `Im(z)^2 <= 1-2*t` for every zero of the `n`th `cosh` approximant.
6. Reuse the compiled identity
   `cosh(sqrt(2*t/n)*u)^n -> exp(t*u^2)` and its uniform integrable error majorant to obtain
   compact-uniform convergence of the approximants to the exact `H_t`.
7. If the limit has a zero outside the contracted closed strip, choose an isolating closed ball
   disjoint from that strip. Jensen zero persistence transfers a zero into a late approximant,
   contradicting step 5.
8. Set `t=1/2`; the right side becomes zero, and nonnegativity of `Im(z)^2` forces `Im(z)=0`.

The implementation may replace this architecture only if it proves the same quantitative
endpoint and records the stronger source theorem used. No imported theorem may hide the
strip-preservation premise as an axiom.

## Existing support and missing dependencies

Available and public:

- the exact `H_0`/xi coordinate and strict strip `-1 < Im(z) < 1`;
- source positivity and nonvanishing at spatial zero;
- entire order at most one and constant-prefactor genus-one Hadamard factorization;
- vertical-average and finite `cosh`-iteration identities;
- compact-uniform forward heat-multiplier convergence;
- arbitrary-multiplicity Jensen zero persistence;
- exact two-time forward preservation after a good time is known.

Missing at selection time:

- conjugation symmetry packaged for the source approximants;
- equality of analytic zero multiplicities under conjugation;
- a conjugation involution on the divisor index;
- the paired Weierstrass-factor strip inequality;
- an entire-function vertical-average strip-contraction theorem;
- the finite-iteration squared-strip invariant.

## Adversarial tests

- The factor of two must give `1-2*t`, not `1-t` or `1-4*t`.
- At `t=0`, the result must follow from the strict source strip without assuming RH.
- At `t=1/2`, the strip width must be exactly zero; a positive epsilon remainder is rejected.
- Arbitrary multiplicities and infinitely many zeros are allowed. No zero trajectory, simplicity,
  spacing, or finite polynomial surrogate may be assumed.
- Real zeros are fixed points of conjugation and must not be accidentally discarded or counted
  with a false strict-pair argument.
- The `n=0` approximation convention may not be used to divide by zero; the strip induction is
  over positive `n`, while the limit remains indexed by all sufficiently large naturals.
- Limit persistence must exclude a zero outside the full closed strip, including points on either
  side, rather than only treat the upper half-plane.
- The endpoint may not rely on the already-proved forward theorem with an unproved earlier good
  time; that would be circular.

## Sources and originality boundary

- N. G. de Bruijn, *The roots of trigonometric integrals* (1950), proved the classical strip
  contraction and the unconditional half-time upper bound.
- B. Rodgers and T. Tao, *The de Bruijn-Newman constant is non-negative*, arXiv `1801.05914`,
  uses the same normalization and records that de Bruijn proved all zeros real for `t >= 1/2`.
- P. Branden and M. Chasse, *Classification theorems for operators preserving zeros in a strip*,
  arXiv `1402.2795`, states the shifted Jensen contraction
  `mu -> sqrt(max(mu^2-a^2,0))` and the heat contraction
  `mu -> sqrt(max(mu^2-2*t,0))`, including finite-order entire extensions.

This campaign reconstructs known mathematics in Lean. It makes no originality claim.

## DAG position and accounting

- `node_id`: H6-H2d
- `gap_id`: H6 threshold nonemptiness dependency of G8
- `relation_to_RH`: proves one positive good time and the classical upper bound `Lambda <= 1/2`;
  it does not prove the RH-equivalent time-zero predicate
- `assumption_frontier_before`: exact source family, heat evolution, zero coordinate, time-zero
  strict strip, closedness, and forward preservation are public
- `hard_gap_before`: threshold nonemptiness/upper-time existence, H6-E/G8, W2/G7, M2/G3, and RH
  are open
- `expected_hard_gap_delta`: 0
- `expected_route_infrastructure_delta`: 1

Success closes threshold nonemptiness and supplies the classical half-time upper bound only. A
finite real Newman threshold, the sharper `0.22` bound, `Lambda <= 0`, and RH remain open.

## Success, falsification, and stop criteria

- `success_criterion`: both fixed endpoints compile; the conjugation-multiplicity, paired-factor,
  strip-average, finite-iteration, and limit-persistence witnesses are registered; exact Targets
  and TargetChecks compile; selected axiom prints are standard-only; forbidden scans,
  `git diff --check`, the full build, and public implementation CI pass.
- `falsification_criterion`: a fixed factor, strip-width, heat-sign, scale, multiplicity-pairing,
  or limit clause is false for the compiled normalization. Record the exact counterexample or
  compiler-checked contradiction without weakening the endpoint.
- `dependency_gap`: if the endpoint cannot be kernel-closed, record the first missing theorem and
  its exact hypotheses as an OBS node. A finite-polynomial theorem alone is not success.
- `local_stop`: close only after both exact endpoints and all gates pass, or record
  `DEPENDENCY_GAP_IDENTIFIED`, `FALSIFIED`, or `NO_PROGRESS` and return to route selection. A local
  stop never pauses the persistent RH Goal.

No Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Public preregistration gate

Pending. Record the immutable commit, run, build job, and duration before proof-source edits.
