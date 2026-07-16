# H6 Reverse-Heat Li Transfer Falsification Preregistration

Date: 2026-07-17

Campaign: `AUDIT-20260717-H6-REVERSE-HEAT-LI-01`

Mode: `FALSIFICATION`

Status: `LOCAL_PREREGISTERED_PUBLIC_CI_PENDING`

## Route selection

Fresh selection after the public H10-B closure compares six materially different candidates:

1. direct W2/G7 positivity through a global pole/archimedean/prime cancellation identity;
2. direct M2/G3 target coupling for the exact positive-natural Baez-Duarte span;
3. H6-Q, the all-real-zero assertion for `H_(1/5)`;
4. generic backward transfer of positive-time H6 real-rootedness or Li positivity to time zero;
5. H1-B/H2-B finite count infrastructure;
6. another RH-equivalent criterion in the Speiser, arithmetic, or heat-Li families.

The W2 termwise sign mechanism is already falsified, and no concrete new global cancellation
identity is available. The M2 projection, ladder-frequency, sparse-frame target, and recent-source
branches have recorded exact obstructions, with no new target-coupling family selected here. H6-Q
requires global nonvanishing and interval-arithmetic infrastructure not present in the fixed tree.
H1-B/H2-B and another equivalence have lower immediate information value. Candidate 4 has a
fully explicit finite model that can either compile or fail at a precise algebraic boundary, and
directly tests a false-progress pattern adjacent to H6-X and H6-E.

## Exact mathematical endpoint

Define the entire two-variable polynomial heat family

`F_t(s) = (s - 1/2)^2 - 1/16 + t/2`.

For an entire function `f` nonzero at `1`, define its generalized second Li value by

`Li2(f) = 2 * (f'/f)(1) + (f'/f)'(1)`.

The indivisible falsification endpoint proves all of the following:

1. `F_t(1-s)=F_t(s)` for every complex `t,s`;
2. `partial_t F_t(s)=(1/4)*partial_s^2 F_t(s)` and the family is entire in both variables;
3. `F_t(1) != 0` for every real `t>=0`;
4. every zero of `F_1` has real part `1/2`;
5. `F_0(3/4)=0` and `3/4` is not on the critical line;
6. `Li2(F_0)=-64/9<0`, whereas `Li2(F_1)=448/121>0`.

Thus the heat PDE, reflection symmetry, positive-time critical-line zeros, and nonvanishing at the
Li base point do not generically transfer Li positivity backward in time. Any successful H6
argument must use additional structure of the actual theta kernel or its zero dynamics.

## Proposed Lean interface

```lean
def h6AuditHeatXiQuadratic (t s : ℂ) : ℂ :=
  (s - 1 / 2) ^ 2 - 1 / 16 + t / 2

def h6AuditSecondLiValue (f : ℂ → ℂ) : ℂ :=
  2 * logDeriv f 1 + deriv (logDeriv f) 1

theorem h6AuditHeatXiQuadratic_reflection (t s : ℂ) :
    h6AuditHeatXiQuadratic t (1 - s) = h6AuditHeatXiQuadratic t s

theorem h6AuditHeatXiQuadratic_heatEquation (t s : ℂ) :
    deriv (fun u : ℂ => h6AuditHeatXiQuadratic u s) t =
      (1 / 4) * deriv (deriv (h6AuditHeatXiQuadratic t)) s

theorem h6AuditHeatXiQuadratic_one_ne_zero_of_nonneg
    (t : ℝ) (ht : 0 ≤ t) :
    h6AuditHeatXiQuadratic t 1 ≠ 0

theorem h6AuditHeatXiQuadratic_one_allZerosOnCriticalLine :
    ∀ s : ℂ, h6AuditHeatXiQuadratic 1 s = 0 → OnCriticalLine s

theorem h6AuditHeatXiQuadratic_zero_offLine_witness :
    h6AuditHeatXiQuadratic 0 (3 / 4) = 0 ∧ ¬ OnCriticalLine (3 / 4 : ℂ)

theorem h6AuditSecondLiValue_zero :
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 0) = -64 / 9

theorem h6AuditSecondLiValue_one :
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 1) = 448 / 121
```

The implementation may package these clauses into one existential counterexample theorem, but it
may not weaken the PDE, reflection, all-zero, nonvanishing, off-line witness, or exact Li-value
clauses.

## Relation to RH and DAG

- `node_id`: H6-H/H6-E
- `gap_id`: G8
- `relation_to_RH`: obstruction below a proposed RH-strength reverse-time transfer
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open
- `expected_hard_gap_delta`: 0
- `expected_obstruction_node`: `OBS-H6-REVERSE-HEAT-LI-01`

The countermodel does not concern the actual `deBruijnNewmanH` zeros and does not falsify RH. It
falsifies only an inference from generic heat, symmetry, base-point nonvanishing, and later
real-rootedness data. At a fixed time, the valid Li/Bombieri-Lagarias equivalence is unchanged.

## Sources and originality boundary

- Rodgers-Tao, *The de Bruijn-Newman constant is non-negative*, supplies the canonical heat family
  and one-way zero-dynamics context.
- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function*,
  supplies the audited normalization and positive-time upper-bound setting.
- Xian-Jin Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, supplies the
  Li coefficient convention.

A targeted primary-source search found the standard threshold and heat-zero dynamics but no claim
that the generic premises above transfer Li positivity backward. The polynomial is an explicit
project countermodel, not a novelty or priority claim.

## Success, falsification, and stop criteria

- `success_criterion`: all seven exact declarations compile, an exact aggregate witness is placed
  in TargetChecks, selected axioms are standard-only, scans and the full build pass, and public CI
  independently verifies the implementation.
- `falsification_criterion`: any exact clause fails for the registered polynomial, especially the
  all-zero statement or one of the two Li constants. Record the compiler boundary rather than
  substituting a different polynomial after proof edits.
- `forbidden_success`: proving only the PDE, one explicit zero, or an informal numerical sign;
  dropping nonvanishing at `1`; replacing all zeros at time one by two listed roots; or changing
  the Li convention.
- `local_stop`: close when the countermodel is compiled and audited, or when one registered clause
  is refuted and the exact failure is recorded. Do not continue into a generic polynomial library.

No Lean proof source has been edited in this campaign before this preregistration.
