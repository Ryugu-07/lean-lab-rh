# G4-F5 Burnol Full Sum And Natural Transfer Pre-Registration

Date: 2026-07-14

Batch ID: `BATCH-20260714-G4-F5`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F5`
- `work_class`: `SOURCE_FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: published

Close the final fixed Burnol edge in one batch: identify the source constant as the half-power of
the full nonnegative `ENNReal` sum over all project nontrivial zeta zeros, prove the continuous
distance lower bound from every finite F4 bound, and transfer it along `lambda=1/N` to the finite
positive-natural kernel distances. Neither a generic `tsum` lemma nor a subsequence liminf wrapper
alone closes F5.

## Primary Source And Scope

Jean-Francois Burnol, *A lower bound in an approximation problem involving the zeros of the
Riemann zeta function*, arXiv `math/0103058v2`, TeX source SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.

- Lines 649-653 state the full-zero lower bound.
- Lines 655-670 prove every finite-zero lower bound and conclude by allowing the finite set to
  vary; F4 now formalizes that finite argument exactly.
- The natural-subspace transfer is not an additional claim in those source lines. It is the
  checked project consequence of F0's inclusion `V_N <= B_(1/N)`, distance inequality
  `D(1/N) <= d_N`, and convergence `1/N -> 0+`.

The source theorem is retained under `hRH : RiemannHypothesis`, as fixed by the G4 dependency
audit. No off-critical or unconditional branch is part of this batch.

## Exact Definitions And Endpoints

Define the nonnegative real contribution

```lean
def burnolZeroContribution
    (rho : {rho : Complex // IsNontrivialZero rho}) : Real :=
  (burnolZetaZeroMultiplicity (rho : Complex) : Real) ^ 2 /
    norm (rho : Complex) ^ 2
```

and the extended full constant

```lean
def burnolFullZeroLowerConstant : ENNReal :=
  (∑' rho : {rho : Complex // IsNontrivialZero rho},
    ENNReal.ofReal (burnolZeroContribution rho)) ^ (1 / 2 : Real)
```

`TargetChecks.lean` must witness the following two theorem types, up to local notation:

```lean
theorem RiemannHypothesis.burnolDistance_liminf_ge_fullZeroSum
    (hRH : RiemannHypothesis) :
    burnolFullZeroLowerConstant ≤
      Filter.liminf (fun lambda : Real =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Set.Ioi 0))

theorem RiemannHypothesis.baezDuarteNaturalDistance_liminf_ge_fullZeroSum
    (hRH : RiemannHypothesis) :
    burnolFullZeroLowerConstant ≤
      Filter.liminf (fun N : Nat =>
        ENNReal.ofReal (baezDuarteNaturalDistance N) *
          ENNReal.ofReal (Real.sqrt (Real.log (N : Real))))
        Filter.atTop
```

The `ENNReal` constant intentionally permits value `top`; no summability or finiteness of the
full zero sum may be assumed. The natural endpoint is an asymptotic liminf statement. This batch
does not claim the stronger and generally unjustified pointwise inequality with the exact limiting
constant for every `N`.

## Full-Sum Surface

The implementation must prove:

- every `burnolZeroContribution rho` is nonnegative;
- for every finite zero set, `ENNReal.ofReal (sqrt (finite real sum))` equals the half-power of
  the corresponding finite `ENNReal` sum;
- `ENNReal.tsum_eq_iSup_sum` and the positive-rpow order isomorphism identify the full constant
  with the supremum of those finite constants;
- the finite F4 theorem bounds every member of that supremum.

No enumeration, countability, summability, or global zero-density estimate is required or allowed
as an unchecked premise.

## Natural-Transfer Surface

Let `F(lambda)` be the continuous scaled-distance expression and `G(N)` the natural expression.
The implementation must prove:

- `Tendsto (fun N => (N : Real)⁻¹) atTop (nhdsWithin 0 (Set.Ioi 0))` gives
  `liminf F <= liminf (F ∘ (1/N))` with the correct filter direction;
- eventually `0 < N`, F0 gives `D(1/N) <= d_N`;
- for positive `N`, `burnolLogScale ((N : Real)⁻¹) = Real.log (N : Real)`;
- the eventual pointwise inequality passes through `ENNReal.ofReal`, multiplication, and liminf.

## Batch Gates

- Gate A defining the full constant or proving finite-sum conversion does not close F5.
- Gate B the full continuous zero-sum bound without natural transfer does not close F5.
- Gate C a natural subsequence bound retaining `burnolLogScale (1/N)` without proving the exact
  `log N` normalization does not close F5.
- No `sorry`, `admit`, project `axiom`, unchecked `constant`, `opaque` premise, source theorem
  postulated as a variable, `native_decide`, or resource-limit relaxation is permitted.
- G4 may be marked complete only after exact targets, transitive axiom audit, full local build,
  clean scans, public commit, and public CI all pass.

## Frontier

- `hard_gap_before`: F0-F4 complete; F5 open and selected; M2/G3 parked and unchanged.
- `assumption_frontier_before`: the full finite-supremum passage and natural subsequence transfer
  remain external to the checked theorem graph.
- `expected_hard_gap_delta`: close F5 and therefore the fixed G4/B1 source-formalization node only.
- `hard_gap_after_on_success`: G4/B1 complete; M2/G3 remain parked and unchanged.

## Result Rules

- `KNOWN_THEOREM_FORMALIZED`: both exact endpoints compile and pass all local and public gates.
- `DEPENDENCY_GAP_IDENTIFIED`: a precise missing sum/filter theorem is isolated without adding it
  as a premise; F5 remains selected.
- `BRANCH_FALSIFIED`: the full-sum normalization or liminf transfer direction contradicts the
  checked finite theorem or F0 inclusion.
- `NO_PROGRESS`: only generic order/filter wrappers compile.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no

## Local Verification Result

Both fixed endpoints are implemented in `LeanLab/Riemann/BurnolFullLowerBound.lean`. Exact target
witnesses and transitive axiom checks pass; each endpoint depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The full 8615-job build, forbidden-token/declaration/resource
scans, and `git diff --check` pass. This is a provisional `KNOWN_THEOREM_FORMALIZED` result pending
the required public commit and public Lean Action gate; F5 and G4 are not yet marked complete.

## Published Result

Implementation commit `9edf524877c7fcfd2112d50095eb021f3da12b0a` passed public Lean Action
CI run `29352792330`, build job `87152928492`, in 2m23s. Both exact endpoints and all fixed batch
gates are therefore public and verified. Final classification: `KNOWN_THEOREM_FORMALIZED`; close
F5 and G4/B1. M2/G3 remains parked and unchanged.
