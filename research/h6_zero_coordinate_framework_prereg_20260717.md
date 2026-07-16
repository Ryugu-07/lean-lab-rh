# H6 Zero-Coordinate Framework Preregistration

Date: 2026-07-17

Campaign: `CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01`

Mode: `LITERATURE`

Status: `PUBLIC_IMPLEMENTATION_COMPLETE_EVIDENCE_PENDING`

## Route selection

The public reverse-heat Li countermodel eliminates a generic backward-transfer shortcut but leaves
the actual H6 route untouched. Fresh selection compares H1/H2 finite-count wrappers, direct
M2/G3 and W2/G7 re-entry, H6-Q, H6-X, and the first open H6-H2 dependency.

- H1-B and H2-B are useful count bookkeeping but do not shorten an RH hard gap.
- The existing M2 projection and W2 termwise-prime mechanisms have exact compiled obstructions;
  no materially new approximant or global cancellation identity is currently available.
- H6-Q requires a global certified nonreal-zero exclusion at `t=1/5`, beyond the present library.
- H6-X requires a source-faithful zero coordinate and all-real-zero predicate before its analytic
  hypotheses can be stated without ambiguity.

The selected indivisible endpoint fixes that coordinate framework for the already compiled exact
source family. It is not a proof of RH and does not claim forward heat preservation or a Newman
threshold.

## Exact mathematical endpoint

Define

`AllZerosReal(t) := forall z in C, H_t(z)=0 -> Im(z)=0`

and the inverse critical-strip coordinate

`z(s) := -i*(2*s-1)`.

Compile all four clauses:

1. For every complex `z`,
   `H_0(z)=0 <-> IsNontrivialZero((1+i*z)/2)`.
2. For every complex `s`,
   `H_0(z(s))=0 <-> IsNontrivialZero(s)`.
3. Every zero of `H_0` lies in the strict source strip `-1 < Im(z) < 1`.
4. `Mathlib.RiemannHypothesis <-> AllZerosReal(0)`.

Clause 4 is RH-equivalent. Compiling the equivalence changes no unconditional truth value; it
aligns the exact H6 endpoint with the project target.

## Proposed Lean interface

The implementation target is `LeanLab/Riemann/DeBruijnNewmanZeros.lean`:

```lean
def deBruijnNewmanAllZerosReal (t : ℝ) : Prop :=
  forall z : ℂ, deBruijnNewmanH t z = 0 -> z.im = 0

def deBruijnNewmanZeroCoordinate (s : ℂ) : ℂ :=
  -Complex.I * (2 * s - 1)

theorem deBruijnNewmanH_zero_iff_isNontrivialZero (z : ℂ) :
    deBruijnNewmanH 0 z = 0 ↔
      IsNontrivialZero ((1 + Complex.I * z) / 2)

theorem deBruijnNewmanH_zeroCoordinate_eq_zero_iff (s : ℂ) :
    deBruijnNewmanH 0 (deBruijnNewmanZeroCoordinate s) = 0 ↔
      IsNontrivialZero s

theorem deBruijnNewmanH_zero_im_mem_Ioo {z : ℂ}
    (hz : deBruijnNewmanH 0 z = 0) :
    z.im ∈ Set.Ioo (-1) 1

theorem riemannHypothesis_iff_deBruijnNewmanAllZerosReal_zero :
    RiemannHypothesis ↔ deBruijnNewmanAllZerosReal 0
```

## Definition and witness alignment

- The source coordinate is exactly `s=(1+i*z)/2`, inherited from
  `deBruijnNewmanH_zero_eq_riemannXi`; its inverse is exactly `z=-i*(2*s-1)`.
- The factor `1/8` must be discharged as nonzero rather than silently normalized away.
- `isNontrivialZero_iff_riemannXi_eq_zero` supplies the already audited exclusion of the pole and
  trivial-zero boundary cases.
- The strip is strict: `s.re` lies in `(0,1)`, hence `z.im=1-2*s.re` lies in `(-1,1)`.
- The all-real predicate quantifies every complex zero. No finite-height, simple-zero,
  multiplicity-free, or real-axis-only surrogate is accepted.
- This campaign aligns zero locations only. It makes no multiplicity-preservation claim.

## Adversarial tests

- Test `s=0` and `s=1`, corresponding to `z=i` and `z=-i`; neither may become an `H_0` zero.
- Check the sign of `z.im=1-2*s.re`; reversing it still preserves the interval but breaks the
  exact coordinate and must be detected by the inverse identity.
- Check both directions of the coordinate theorem, especially surjectivity from an arbitrary
  nontrivial zero `s`.
- Check that `z.im=0` is equivalent to `s.re=1/2`, not to `z.re=0`.
- Check all complex zero quantifiers and avoid importing RH in either direction except as the
  explicit hypothesis of the forward implication.

## Sources and originality boundary

- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function*
  (arXiv `1904.12438`), fixes the displayed `H_t`, the `H_0` xi coordinate, and the equivalence of
  RH with the `t=0` all-real-zero statement.
- Rodgers and Tao, *The de Bruijn-Newman constant is non-negative* (arXiv `1801.05914`), uses the
  same source family and threshold convention.
- The strict critical-strip bounds and `Mathlib.RiemannHypothesis` predicate are already compiled
  project/mathlib facts.

This is a source-aligned known-theorem formalization, not an originality claim.

## DAG position and accounting

- `node_id`: H6-H2
- `gap_id`: G8 dependency
- `relation_to_RH`: clause 4 is exactly equivalent to RH
- `assumption_frontier_before`: exact H6-B source normalization and H6-H1 entire heat equation;
  no compiled all-real-zero coordinate framework
- `hard_gap_before`: H6-H2, H6-E/G8, W2/G7, M2/G3, and RH open
- `expected_hard_gap_delta`: 0
- `expected_route_infrastructure_delta`: 1

Success closes only the zero-coordinate and all-real-predicate subedge of H6-H2. De Bruijn forward
preservation, nonempty upper-ray existence, threshold closedness, the bound `Lambda<=0`, and RH
remain open.

## Success, falsification, and stop criteria

- `success_criterion`: all four exact clauses compile; Targets and an exact aggregate
  TargetCheck are registered; selected axiom prints are standard-only; forbidden scans,
  `git diff --check`, full build, and public implementation CI pass.
- `falsification_criterion`: any map, inverse, strict-strip, or RH-equivalence clause fails under
  the fixed source normalization. Record the exact compiler or mathematical boundary rather than
  weakening the endpoint.
- `forbidden_success`: one implication only, a real-input theorem, a non-strict strip, a text-only
  target, or an equivalence using a newly defined surrogate for RH.
- `local_stop`: close after the exact coordinate framework is compiled and audited, or after a
  fixed clause is refuted and its exact obstruction is recorded. Do not expand into forward heat
  preservation in the same campaign.

No Lean proof source has been edited in this campaign before this preregistration.

## Public preregistration gate

Preregistration commit `8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e` passed public Lean Action CI
run `29512089828`, build job `87667820977`, in `2m17s` (`2026-07-16T15:38:51Z` to
`2026-07-16T15:41:08Z`). Lean proof-source edits begin only after this gate.

## Registered implementation result

`DeBruijnNewmanZeros.lean` compiles every fixed clause without changing the coordinate, strip, or
quantifiers. The exact aggregate theorem is `deBruijnNewman_zeroCoordinate_framework`. Both
boundary witnesses, exact TargetCheck, five standard-only axiom prints, empty forbidden scan,
`git diff --check`, and the 8,687-job full build pass locally. Classification is
`KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and `route_infrastructure_delta=1`.
Implementation commit `0283db6a11ef452a7241e17c535744677272a7d1` passed public Lean Action CI run
`29513380203`, build job `87672181193`, in `1m59s` (`2026-07-16T15:56:06Z` to
`2026-07-16T15:58:05Z`). Immutable evidence backfill and its independent public CI remain before
closure.
