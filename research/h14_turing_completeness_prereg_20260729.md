# H14 Turing Completeness Consumer Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H14-TURING-COMPLETENESS-CONSUMER-01`

Node: `H14-TURING-COMPLETENESS-CONSUMER-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `FULL_TURING_COMPLETENESS_CONSUMER_SUCCESS / IMPLEMENTATION_PUBLIC /
IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Source statement

Turing-style verification has two logically separate inputs:

1. a rigorously certified list of actual zeros, with every listed zero located on the critical
   line;
2. an analytic count proving that the list contains every zero in the finite region, with
   multiplicity.

Only their conjunction proves finite-height RH. A list of line zeros without a completeness
count does not exclude a missing off-line zero.

The project already compiles the analytic identity

```text
integral_boundary Gamma (xi'/xi)
  = 2*pi*i * sum_{multiplicity indices strictly inside Gamma} 1
```

for a zero-free rectangle boundary. This campaign connects that actual xi identity to the exact
finite candidate-exhaustion theorem.

## Exact fixed endpoint

Create `LeanLab/Riemann/TuringCompletenessConsumer.lean` only after the public preregistration
gate. Compile the following without `sorry`.

1. Define `turingXiZeroIndexFinset l r b t` from
   `finite_riemannXiZeroStrictlyInsideRectangle`.
2. Prove exact membership:

   ```text
   p in turingXiZeroIndexFinset l r b t
     iff riemannXiZeroStrictlyInsideRectangle l r b t p.
   ```

3. Prove the unweighted finite argument-principle count:

   ```text
   rectangleBoundaryIntegral (logDeriv riemannXi) l r b t
     = 2*pi*i * card(turingXiZeroIndexFinset l r b t)
   ```

   under `l<r`, `b<t`, and a zero-free xi boundary.
4. Define `TuringXiRectangleCertificate candidates l r b t` to require:

   - every candidate is an actual divisor index inside the rectangle;
   - every candidate value lies on the critical line;
   - the candidate cardinality equals the full multiplicity-bearing index cardinality.

5. Prove that any such certificate makes `candidates` equal to the full index finset and places
   every actual multiplicity index in the rectangle on the critical line.
6. Use `exists_riemannXiDivisorZeroIndex_val_iff` to prove the value-level theorem: every actual
   `IsNontrivialZero rho` strictly inside the rectangle lies on the critical line.
7. Define a boundary-count certificate that replaces direct cardinality equality by the
   candidate boundary-integral equality. Use the actual xi count theorem and cancellation of
   `2*pi*i` to derive the rectangle certificate and value-level conclusion.
8. Compile a finite negative control with a proper candidate subset whose listed points are all
   on the critical line while the ambient set contains an off-line point.
9. Package only these fields in an aggregate certificate.

Exact names may follow local style. The analytic zero index must be the project's actual
`RiemannXiDivisorZeroIndex`; replacing it by a synthetic zero set does not satisfy the endpoint.

## Multiplicity and definition alignment

`RiemannXiDivisorZeroIndex` repeats a zero according to its analytic multiplicity. Therefore
Finset cardinality is the multiplicity-bearing zero count used by the argument principle. The
candidate object is also a Finset of these indices, so exact roots and their multiplicities are
proof obligations rather than assumptions hidden in a natural-number count.

The value-level conclusion uses the established equivalence between actual nontrivial zeta zeros
and xi zeros. No simplicity hypothesis may be introduced. Platt--Trudgian prove simplicity in
their concrete computation, but completeness and finite critical-line location do not logically
require it.

## Success criteria

`FULL_TURING_COMPLETENESS_CONSUMER_SUCCESS` requires all nine clauses, a proven Target, an exact
open successor Target, exact TargetChecks, selected transitive axiom prints with standard axioms
only, empty forbidden scans, warning-as-error compilation, a full build, and every public CI
gate.

`MEANINGFUL_TURING_PARTIAL` requires clauses 1, 2, 4--6, and 8. The first unavailable
argument-principle count or boundary-to-cardinality theorem must be recorded exactly and must not
be introduced as a proved premise.

`FALSIFIED` applies if the divisor-index cardinality fails to match analytic multiplicity or if
candidate subset plus exact cardinality does not force exhaustion. A minimal compiled
counterexample and corrected statement are required.

## Negative controls and claim boundary

- `NO_COUNT_NO_COMPLETENESS`: line location of every candidate does not exclude omitted zeros.
- `NO_ACTUAL_WITNESS_NO_COMPLETENESS`: a same-size list of synthetic points is not a certified
  zero list.
- `MULTIPLICITY`: counting distinct complex values is insufficient unless multiplicities are
  separately certified.
- `BOUNDARY`: the argument-principle identity requires no xi zero on the rectangle boundary.
- `FINITE_ONLY`: exhaustion of one finite rectangle says nothing about zeros above it.
- `NO_NUMERICAL_CLAIM`: no interval arithmetic result or numerical height is imported as a Lean
  premise.
- `NO_RH`: the global tail reduction, H14-to-RH promotion, and RH remain open.

Expected classification:

- `historical_subroute_coverage_delta=1`;
- `turing_positive_consumer_delta=1` only under full success;
- `actual_xi_count_bridge_delta=1` only if clause 3 compiles;
- `certified_height_delta=0`;
- `global_tail_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source, Target, TargetCheck, axiom-audit entry, or aggregate import may be
created or edited until this docs-only preregistration passes public Lean Action CI.

The persistent RH Goal remains active. Local completion returns to fresh historical route
selection.
