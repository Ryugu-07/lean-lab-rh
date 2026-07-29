# H7 Connes Nested-Projection Positive-Type Attempts

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H7-CONNES-PROJECTION-DEFECT-01`

Node: `H7-CONNES-NESTED-PROJECTION-POSITIVE-TYPE-01`

Status: `LOCAL_FULL_SUCCESS_AUDITED_PUBLIC_IMPLEMENTATION_REQUIRED`

## Fixed question

Does the exact nested-projection premise in Connes 1998 equations `(23)`--`(25)` force the
cutoff defect trace to be positive on every convolution square, and does that implication fail
when nesting is removed?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | The repository has deep Weil-form infrastructure, finite-prime spectral matrices, and a Berry--Keating half-line obstruction, but no theorem card for the original Connes absorption-spectrum trace mechanism. | Select the first exact algebraic hinge in Connes 1998 rather than attempting the full adèle-class construction at once. |
| 2 | `PRIMARY_SOURCE_AUDIT` | Theorem 5 equations `(23)`--`(25)` use containment of orthogonal projections to make a trace distribution positive on `f*f*`; the later limit identifies it with the Weil distribution. | Freeze the nested-projection trace identity and a no-nesting counterexample as the bounded endpoint. |
| 3 | `PREREGISTRATION` | Full, partial, falsification, and claim-boundary criteria are fixed. The finite theorem cannot stand in for trace class, the global limit, or Weil positivity. | Publish docs only. Do not edit `LeanLab/` until public CI passes. |
| 4 | `PUBLIC_GATE` | Preregistration commit `59a6d8aa74fb48c3123e391e50e2e932408bcf66` passed Lean Action run `30411132179`, build job `90447227409`, in `1m33s`. | Admit production proof edits under the frozen statement. |
| 5 | `FINITE_ALGEBRA` | From the six exact source-style hypotheses, `H=P-Q` is self-adjoint and idempotent. Trace cyclicity rewrites `Trace(H*A*Aᴴ)` as `Trace((H*A)*(H*A)ᴴ)`. | Prove an exact matrix trace/Frobenius-square identity rather than use an abstract positivity lemma. |
| 6 | `ZERO_CHARACTERIZATION` | The exact trace is a finite sum of nonnegative `Complex.normSq` terms. | Compile real nonnegativity, zero imaginary part, and vanishing iff `H*A=0`. |
| 7 | `FALSIFICATION_CONTROL` | In dimension one, `P=0` and `Q=1` are each orthogonal projections, but they are not nested and the defect trace at `A=1` has real part `-1`. | Record nesting as the exact algebraic boundary; individual projection laws are insufficient. |
| 8 | `LOCAL_AUDIT` | The 192-line module, proven Target, eight exact checks, seven standard-only axiom prints, empty scans, warning-as-error compiles, `git diff --check`, and full build `8793/8793` pass. | Classify `FULL_SUCCESS / SOURCE_POSITIVE_TYPE_HINGE_FORMALIZED`; freeze and publish the implementation next. |

## Current frontier

- `compiled`: defect self-adjoint idempotence, exact trace-as-Frobenius-square identity,
  nonnegativity, zero characterization, and the `1 x 1` no-nesting counterexample.
- `interpretation`: the finite positive-type inference itself has no hidden analytic content;
  all number-field pressure lies before it in constructing the actual nested projections and
  after it in trace-class control and the distributional limit.
- `open_after_success`: actual adèle projections, number-field trace class, prolate cutoff
  asymptotics, distributional limit, full Weil positivity, H7, and RH.
- `next_gate`: frozen implementation commit and independent public CI.
- `protected_files`: the six inherited modified/untracked files remain untouched and unstaged.
- `global_goal`: active.
