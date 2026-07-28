# H14 Turing Completeness Consumer Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H14-TURING-COMPLETENESS-CONSUMER-01`

Node: `H14-TURING-COMPLETENESS-CONSUMER-01`

Classification: `FULL_TURING_COMPLETENESS_CONSUMER_SUCCESS / IMPLEMENTATION_PUBLIC`

## Kernel-checked result

`LeanLab/Riemann/TuringCompletenessConsumer.lean` compiles all nine preregistered clauses without
`sorry`.

1. `turingXiZeroIndexFinset` is the finite set of actual multiplicity-bearing xi divisor indices
   strictly inside an open rectangle.
2. `mem_turingXiZeroIndexFinset_iff` gives its exact membership predicate.
3. `rectangleBoundaryIntegral_logDeriv_riemannXi_eq_turingXiZeroIndexFinset_card` specializes the
   existing weighted xi argument principle at constant weight one and identifies the divisor
   finsum with Finset cardinality.
4. `TuringXiRectangleCertificate` requires candidate inclusion, critical-line location, and exact
   cardinality.
5. `TuringXiRectangleCertificate.candidates_eq_actual` proves finite exhaustion, and
   `actual_indices_on_line` transfers line location to every actual interior divisor index.
6. `TuringXiRectangleCertificate.nontrivial_zeros_on_line` uses the existing xi-divisor value
   bridge to reach every actual `IsNontrivialZero` in the rectangle.
7. `TuringXiBoundaryCountCertificate.toRectangleCertificate` cancels the nonzero
   `2*pi*i` factor against the actual xi count. Its exhaustion and actual-zero consumers compile.
8. `exists_line_candidate_proper_subset_with_offline_ambient` is the finite negative control:
   without exact counting, a verified all-line candidate subset may omit an off-line point.
9. `turingCompletenessConsumer_endpoint` packages only the fixed finite consumer.

The candidate type is `RiemannXiDivisorZeroIndex`, so repeated values retain analytic
multiplicity. No simplicity assumption is used.

## Mechanical audit

- The 281-line production module compiles with `-DwarningAsError=true`.
- `Targets.lean` records one proven Target,
  `H14.computation.turing-completeness-consumer`.
- The exact open successor is
  `H14.computation.turing-numerical-certificate`.
- Eight exact TargetChecks compile: membership, analytic count, direct exhaustion, direct
  actual-zero location, boundary conversion, boundary actual-zero location, negative control,
  and aggregate endpoint.
- Seven selected transitive axiom prints use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Three forbidden scans are empty.
- `git diff --check` passes.
- The full local build passes `8787/8787`.

## Claim boundary

This is the positive logical consumer behind finite Turing-style verification. It does not
construct a candidate zero list, isolate roots, prove boundary nonvanishing at a concrete
height, establish Turing's average estimate, import a numerical zero table, or certify any
finite height. It also does not prove a global tail reduction, H14-to-RH promotion, or RH.

The first open producer is `H14.computation.turing-numerical-certificate`: construct an actual
interval-certified candidate list and boundary-count certificate for one concrete rectangle.
The separate global successor remains `H14.computation.global-tail-reduction`.

## Deltas

- `historical_subroute_coverage_delta=1`;
- `turing_positive_consumer_delta=1`;
- `actual_xi_count_bridge_delta=1`;
- `certified_height_delta=0`;
- `global_tail_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

Frozen implementation `258a9ac8ce69f6dffe6beb4a6a7579845ca2a457` passed public Lean Action
run `30397348488`, build job `90403505298`, in `2m6s`. Immutable evidence CI is required
before final ledger closure.
