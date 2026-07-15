# Sparse Baez-Duarte Target Obstruction Pre-Registration

Campaign: `CAMPAIGN-20260715-SPARSE-OBSTRUCTION-01`

Date: 2026-07-15

## Fixed Position

- `route`: exact Baez-Duarte sparse target coupling
- `work_class`: `FALSIFICATION`
- `previous_evidence`: the published `1/40` lower-frame bound for the kernels indexed by
  `(2^24)^j`
- `hard_gap_before`: M2/G3 parked
- `assumption_frontier_before`: no unconditional membership of
  `baezDuarteComplexTargetL2` in `baezDuarteComplexKernelClosure`
- `expected_hard_gap_delta`: zero
- `intended_close`: `BRANCH_ELIMINATED`
- `novelty_label`: `NOVELTY_UNCHECKED`
- `compaction_since_previous_campaign`: no

This is specific new evidence for one final target-coupling audit of the sparse family. It does
not reopen generic Gram optimization and does not claim that the full positive-natural family is
incomplete.

## Candidate Set

### C1: Explicit Orthogonal Witness

Let `Q = 2^24` and `u_j(x) = sqrt(Q^j) * fract(1/(Q^j*x))`. Define

```text
w(x) =  118*x  on (1/2, 2/3]
       -925*x  on (1/3, 2/5]
       1176*x  on (1/4, 2/7]
          0    elsewhere.
```

The exact rational moments are

```text
sum alpha_k * length(I_k)       = 0,
sum alpha_k * k * integral_I_k x = 0,
sum alpha_k * integral_I_k x     = 1/9.
```

On all three intervals every `j >= 1` kernel is a scalar multiple of `1/x`. The `j = 0` kernel is
`fract(1/x) = 1/x-k` on the interval labelled by `k = 1,2,3`. Hence the first two moment identities
make `w` orthogonal to every sparse kernel, while the last identity gives a nonzero pairing with
the target indicator.

Proposed Lean surface:

```lean
theorem inner_sparseGramKernel_sparseTargetWitness_eq_zero (j : Nat) :
    inner (baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j))
      sparseTargetWitnessL2 = 0

theorem inner_target_sparseTargetWitness :
    inner baezDuarteComplexTargetL2 sparseTargetWitnessL2 = (1 / 9 : Complex)

theorem baezDuarteComplexTargetL2_not_mem_sparseGramKernelClosure :
    baezDuarteComplexTargetL2 ∉ sparseGramKernelClosure
```

- RH strength: strictly weaker than RH. It excludes only the lacunary subfamily; the full natural
  family remains exactly the RH-equivalent family already compiled in the project.
- Fixed-DAG effect: no RH bridge is reduced. A successful proof eliminates the proposed sparse
  target-coupling mechanism.
- Status: **SELECTED CANDIDATE**.

### C2: Coefficient-Limit Reconstruction

Use the lower-frame bound to extract an `ell2` coefficient limit from any convergent sequence of
finite sparse combinations, then analyze its restriction to the first logarithmic cell.

- Adversarial result: C1 would provide a direct continuous functional separating the target, so
  coefficient reconstruction adds no mathematical information.
- Status: `DOMINATED_MECHANISM`; do not formalize in this campaign.

### C3: One-Interval Obstruction

Try to separate the target on only `(1/2,2/3]`.

- Counterexample: on this cell the target satisfies
  `1 = -fract(1/x) + 1/x`, so it lies in the two-dimensional local kernel model.
- Status: `CONJECTURE_FALSIFIED` before Lean admission.

### C4: Two Constant-Weight Pieces

Use only two functions `alpha_k*x*indicator(I_k)` to kill both kernel directions.

- Exact check: the two moment vectors for distinct floor cells are not proportional, so the only
  simultaneous annihilator is zero.
- Status: `REJECTED_ENGINEERING_CHOICE`; three pieces are minimal for this ansatz.

### C5: Every Geometric Ratio Is Incomplete

Generalize C1 immediately to all integer ratios `Q >= 4`.

- Adversarial result: this broadens quantifiers without changing the selected branch decision and
  would require avoidable interval bookkeeping.
- Status: `DEFER`; no generic wrapper or parameterized theorem in this campaign.

## Literature Audit

- Baez-Duarte, arXiv `math/0205003`, proves that the full natural family gives an RH-equivalent
  closure problem. It does not state that the powers of one integer suffice.
- Alouges, Darses, and Hillion, DOI `10.5802/jtnb.1227`, split generalized approximation from
  coefficient control and study structured Gram matrices.
- Ehm, arXiv `2405.06349`, gives exact Nyman-Beurling Gram formulas nearest to the previous sparse
  lower-frame campaign.
- Yang, DOI `10.1016/j.crma.2017.11.021`, studies Nyman-space approximation and geometric sequences
  arising from zero functions; it is not an incompleteness theorem for a geometric dilation
  subsequence.

No source located in this audit states the exact three-interval witness or the exact exclusion of
the `(2^24)^j` family. Novelty therefore remains unchecked rather than claimed.

## Admission And Stop Conditions

Only C1 receives a Lean proof attempt. No numerical observation is a premise. Stop and classify
`NO_PROGRESS` if the exact inner-product alignment, interval formulas, or closure separation fails
after two genuinely different proof mechanisms. If C1 compiles and passes the axiom audit, close
as `BRANCH_ELIMINATED`, leave every RH hard gap unchanged, and return to `ROUTE_SELECTION` with a
different route family.

## Lean Result

Result: `BRANCH_ELIMINATED`

- `sparseTargetWitnessPiece_memLp` packages each compactly supported linear piece in the exact
  positive-half-line `L2` measure.
- `one_eq_neg_fractionalPartKernel_add_div_on_sparseInterval_one` Lean-checks the C3 local
  counterexample, and `sparseTarget_two_piece_moment_determinant` Lean-checks the exact C4
  determinant value `1/600`.
- `inner_baezDuarteKernelL2_sparseTargetWitnessRealL2_eq_zero` proves exact orthogonality for every
  index `(2^24)^j`. The `j=0` case uses the three floor cells; every `j>=1` case reduces to the
  annihilated reciprocal moment.
- `inner_target_sparseTargetWitness` proves the exact complex target pairing is `1/9`.
- `baezDuarteComplexTargetL2_not_mem_sparseGramKernelClosure` uses the orthogonal complement of the
  topological closure to prove that the target is not in the sparse closed span.
- No numerical result, unproved proposition, or additional axiom is used.

The theorem excludes only the registered sparse subfamily. It neither contradicts nor weakens the
compiled RH equivalence for the full positive-natural family. M2/G3 remains parked,
`hard_gap_delta=0`, and novelty remains `NOVELTY_UNCHECKED`. The next state is `ROUTE_SELECTION`
with a different route family.

## Publication Evidence

- implementation commit: `c2e6f086b30fc54b5e0ed6ab2782bf5ef9283a85`
- public Lean Action CI: run `29391437206`, build job `87275634635`, succeeded
