# H6 Heat-Li All-Index Criterion Preregistration

Date: 2026-07-17

Campaign: `LITERATURE-20260717-H6-HEAT-LI-ALL-INDEX-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL`

## Exact definitions

For the existing source-normalized heat family, add

```lean
def deBruijnNewmanHeatLiCoefficient (t : Real) (n : Nat) : Complex :=
  iteratedDeriv (n + 1)
    (fun s : Complex => s ^ n * log (deBruijnNewmanHeatXi t s)) 1 /
      (Nat.factorial n : Complex)
```

The definition must be checked item by item against the project convention: index `n` is the
classical coefficient `lambda_(n+1)`, the base point is `s=1`, and the factorial is `n!`.

## Fixed mathematical endpoint

The campaign succeeds only if Lean proves all of the following without a new hypothesis:

1. for every real `t`, the heat-Xi function is entire of order at most one, reflection symmetric,
   conjugation compatible, and nonzero at `s=0` and `s=1`;
2. for every `t>=0`, its multiplicity-bearing zero divisor satisfies the weighted summability
   needed for the Li zero formula, using the compiled zero strip on `0<=t<=1/2` and all-real
   theorem on `t>=1/2`;
3. for every `t>=0`, the derivative-defined coefficients have the exact compensated,
   symmetry-paired zero formula;
4. for every `t>=0`,

   `deBruijnNewmanAllZerosReal t <->
      forall n, 0 <= (deBruijnNewmanHeatLiCoefficient t n).re`;

5. for every `n`,

   `deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n`;

6. the `t=0` specialization is definitionally and theorem-level compatible with both
   `riemannHypothesis_iff_deBruijnNewmanAllZerosReal_zero` and
   `riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg`.

None of clauses 1-3, either implication alone, or a finite-index specialization is a successful
endpoint.

## Proposed public Lean surface

```lean
theorem deBruijnNewmanHeatLiCoefficient_zero_eq (n : Nat) :
  deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n

theorem deBruijnNewmanAllZerosReal_iff_forall_heatLiCoefficient_re_nonneg
    (t : Real) (ht : 0 <= t) :
  deBruijnNewmanAllZerosReal t <->
    forall n : Nat, 0 <= (deBruijnNewmanHeatLiCoefficient t n).re

theorem deBruijnNewmanHeat_allIndexLi_endpoint :
  (forall n, deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n) /\
  (forall t, 0 <= t ->
    (deBruijnNewmanAllZerosReal t <->
      forall n, 0 <= (deBruijnNewmanHeatLiCoefficient t n).re))
```

Names may be adjusted to local style. The mathematical clauses may not be weakened.

## Source reconstruction

Bombieri-Lagarias prove the abstract zero-multiset criterion under weighted reciprocal
summability. The existing project specializes their dominant transformed-zero argument to the xi
divisor. This campaign must either extract a reusable generic theorem or repeat the argument for
the heat divisor without importing xi-specific facts.

The forward direction uses the reflection pair `rho <-> 1-rho`: on the critical line the
transformed values have modulus one, so each symmetry-paired real contribution is nonnegative. The
reverse direction uses a reflected off-line zero, a finite transformed-radius superlevel,
simultaneous phase recurrence, and reciprocal-square tail domination.

## Known obstacles

- `LiZeroFormula.lean`, `LiSymmetricZeroFormula.lean`, and `LiReverseCriterion.lean` currently
  hard-code `riemannXi` and its divisor type.
- finite order under the affine input `s |-> -i*(2*s-1)` is not yet exposed as a public helper.
- divisor multiplicities must be transported or the heat-Xi divisor must be handled directly.
- the degree-at-most-one Hadamard polynomial contribution must cancel from the Li coefficients by
  reflection/degree; it cannot be silently discarded.
- the negative-time zero strip required for the published weighted hypothesis is not compiled;
  this is why the fixed endpoint is `t>=0`.
- the logarithm is local. Every derivative identity must use the compiled positivity at `s=1`,
  not a global branch of `log`.

## DAG and strength

- `node_id`: H6-X4, an all-index child linking H6-X to H6-E/G8.
- `relation_to_RH`: at `t=0` the endpoint is RH-equivalent; at positive time it characterizes the
  deformed zero set.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `expected_hard_gap_delta`: 0. The campaign compiles a criterion but proves no unconditional
  all-index positivity.
- `expected_route_infrastructure_delta`: 1 only if the complete iff and time-zero alignment pass.
- `novelty_label`: `KNOWN_CRITERION_HEAT_FAMILY_SPECIALIZATION`; no first-formalization claim.

## Falsification criteria

- a heat-Xi zero at `0` or `1`;
- failure of affine order-one growth;
- failure of weighted summability for some `t>=0`;
- a mismatch in coefficient indexing, factorial, or the time-zero definition;
- a real-zero heat function with a negative coefficient;
- an off-real zero set satisfying all coefficient real-part inequalities;
- an unavoidable extra premise not derivable from the exact source family and `0<=t`.

Any such failure closes the campaign as a precise obstruction or falsification. Helpers alone close
as `NO_PROGRESS`, not success.

## Mechanical gates

- exact Targets and complete TargetChecks;
- selected axiom prints for the definition bridge, zero formula, both implications, iff, and
  aggregate endpoint;
- no `sorry`, `admit`, `native_decide`, custom axiom/constant/opaque/unsafe declaration, or resource
  relaxation;
- standalone diagnostic-free compile, full build, `git diff --check`, and public CI;
- M0 definition alignment recorded in the attempt log.

## Public preregistration gate

No Lean proof-source file may be edited before this preregistration commit passes public Lean
Action CI.
