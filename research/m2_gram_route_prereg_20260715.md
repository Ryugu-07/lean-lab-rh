# Exact Baez-Duarte Gram Campaign Pre-Registration

Campaign: `CAMPAIGN-20260715-GRAM-01`

Date: 2026-07-15

## Fixed Position

- `route`: exact Baez-Duarte Gram/projection geometry
- `work_class`: `DISCOVERY` plus `FALSIFICATION`
- `hard_gap_before`: M0, M1, D, and G4 complete; M2/G3 parked
- `assumption_frontier_before`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`
- `expected_hard_gap_delta`: zero unless the campaign unexpectedly proves a source-aligned
  unconditional bridge estimate
- `novelty_label`: `NOVELTY_UNCHECKED`
- `compaction_since_previous_campaign`: yes; fixed DAG and current worktree were re-audited

The normalized physical kernel is

```text
u_n(x) = sqrt(n) * fract(1 / (n*x)),  n >= 1.
```

Under the existing weighted logarithmic isometry, this is a translate of one fixed `L2(R)` vector.
Ehm arXiv `2405.06349`, especially the integral formula in Proposition 3.1, is the nearest exact
published Gram result. General Riesz criteria for dilation systems are also treated in arXiv
`2110.07659`. Neither source has yet been verified to contain the explicit sparse estimate below.

## Candidate Set

### C1: Log-Stationary Normalized Gram

Mathematical statement: for positive parameters, simultaneous scaling does not change normalized
Gram entries; equivalently the entry depends only on the logarithmic ratio.

Proposed Lean surface:

```lean
inner (normalizedContinuousKernel (c * theta))
      (normalizedContinuousKernel (c * phi)) =
  inner (normalizedContinuousKernel theta)
        (normalizedContinuousKernel phi)
```

- RH strength: strictly weaker than RH.
- Adversarial checks: diagonal, swapped parameters, common scaling, numerical ratios.
- Status: `KNOWN_SOURCE_STRUCTURE`, not a novelty candidate. It may be formalized only inside the
  selected batch as one proof input.

### C2: Uniform Coercivity Of The Full Natural Sequence

Mathematical statement: there is `A > 0` such that every finite complex coefficient family obeys

```text
A * sum |c_n|^2 <= ||sum c_n * u_n||^2.
```

- RH strength: does not by itself imply RH, but would uniformly control all normalized finite Gram
  inverses.
- Adversarial check: the logarithmic sample gap `log(n+1)-log(n)` tends to zero. Numerical
  quadrature gives squared adjacent differences `0.3086, 0.2304, 0.1566, 0.1000, 0.0607, 0.0358,
  0.0206` for `n=4,8,...,256`.
- Status: `NUMERICAL_ONLY_REJECTION_SIGNAL`. The mathematical rejection is not admitted as a Lean
  premise until translation continuity and the two-term contradiction compile.

### C3: Elementary Off-Diagonal Envelope

For `0 < theta <= phi`, propose

```text
|inner u_theta u_phi| <= sqrt(theta / phi) * (2 + log(phi / theta)).
```

It comes from the pointwise bounds `0 <= fract(y) <= min(1,y)` and splitting the positive half-line
at `theta` and `phi`.

- RH strength: strictly weaker than RH.
- Adversarial checks: equality-scale boundary, extreme ratios, symmetry, comparison with exact
  Ehm formula. Numerical ratios `1,2,4,16,256,2^24` remain below the proposed envelope.
- Status: `CANDIDATE_SUPPORT_BOUND`. It is not a premise until Lean proves the integral and exact
  `L2` inner-product alignment.

### C4: Explicit Sparse Lower Frame Bound

Let `Q = 2^24`, `n_j = Q^j`, and use the normalized kernels `u_(n_j)`. Propose the exact bound

```text
(1/40) * sum_j |c_j|^2 <= ||sum_j c_j * u_(Q^j)||^2
```

for every finitely supported complex family `c`.

Proposed Lean statement:

```lean
theorem sparseGram_lower_frame_bound
    (c : Nat →₀ Complex) :
    (1 / 40 : Real) * (c.support.sum fun j => norm (c j) ^ 2) <=
      norm (sparseGramCombination c) ^ 2
```

- Intended proof: prove `||u_n||^2 >= 1/24` on the physical interval `(1/2,2/3)`; use C3 and
  `log 2 < 1` to bound distance-`d` correlations by `(2+24*d)/4096^d`; sum both tails and apply
  `2ab <= a^2+b^2` to the finite Gram form.
- RH strength: does not imply RH. The stronger statement that the target belongs to this sparse
  closed span would imply RH and is explicitly out of scope.
- Adversarial checks: two-point systems, boundary constants, finite matrices of sizes 2, 4, 6, 8.
  Numerical minimum eigenvalues are approximately `1.2581, 1.2569, 1.2566, 1.2565`, far above
  `1/40`; this is `NUMERICAL_ONLY`.
- Status: **SELECTED CANDIDATE**. At most this one candidate receives a proof attempt.

### C5: Finite Gram Positivity As A Closure Mechanism

Candidate inference: positivity or invertibility of every finite Gram matrix is sufficient to make
the target projection residual tend to zero.

- RH strength: if valid for the exact target it would prove the RH-equivalent closure statement.
- Adversarial check: `Matrix.posSemidef_gram` makes finite Gram positivity automatic for every
  Hilbert-space family, independent of the target. Invertibility only gives a finite projection;
  it contains no asymptotic residual estimate.
- Status: `REJECTED_MECHANISM`. The selected Lean batch must include a typed finite-dimensional
  witness separating positive-definite Gram data from target closure/residual convergence, or else
  record this item as unverified and not use it.

## Numerical Test Record

- method: weighted-log representatives sampled on a uniform real grid; trapezoidal Gram assembly
- role: falsification guidance only
- normalized diagonal observed: approximately `1.2605`
- full natural minimum eigenvalues for `N=4,8,16,32,64`: approximately
  `0.1102, 0.0822, 0.0463, 0.0232, 0.0127`
- no numerical value is available as a theorem or proof premise

## Admission Decision

Only C4 is selected. C1 and C3 must be batched as source/engineering inputs, not counted as
successor targets. C2 and C5 are falsification obligations. No new target is added to
`Targets.lean`, and no RH progress is claimed.

## Stop And Pivot Conditions

- Stop this campaign if C3 fails, the explicit geometric series does not yield the registered
  `1/40` constant, or the exact kernel/inner-product alignment changes the statement.
- A weaker constant may be accepted only if fixed before rerunning the proof and still follows from
  the same single batch; it is not a new campaign.
- If C4 fails after two genuinely different proof mechanisms, close as `CONJECTURE_FALSIFIED` or
  `NO_PROGRESS` and pivot to R3 or R5. Do not pause the global goal.

## Lean Result

Result: `AUXILIARY_PROPERTY_PROVED`

- C3 is proved by `integral_fractionalPartKernel_mul_le`. Lean splits the positive half-line at
  the two kernel parameters and integrates the exact majorants `1`, `a/x`, and `a*b/x^2`.
- The normalized diagonal is uniformly at least `1/24` by
  `baezDuarteNormalizedKernel_diagonal_lower`, using the physical interval
  `(1/(2*n), 2/(3*n))`.
- For sparse distance `d`, `norm_inner_sparseGram_ne_le` proves the admitted geometric envelope;
  `sum_norm_inner_sparseGram_offDiag_le` proves every finite off-diagonal row sum is at most
  `4/297`.
- `sparseGram_lower_frame_bound` proves the registered `1/40` lower-frame inequality for every
  finitely supported complex coefficient family.
- C5 is discharged by the typed witness `finiteGramWitness_posDef` together with
  `finiteGramWitness_target_orthogonal`: positive-definite finite Gram data can coexist with a
  nonzero orthogonal target.
- C2 remains only a `NUMERICAL_ONLY_REJECTION_SIGNAL`; no rejection theorem was needed or used.

No target-closure membership, residual convergence, or RH implication follows from the sparse
lower frame bound alone. The RH assumption frontier and M2/G3 hard gap are unchanged. The explicit
constant has not been matched exhaustively against the literature, so the novelty label remains
`NOVELTY_UNCHECKED`.
