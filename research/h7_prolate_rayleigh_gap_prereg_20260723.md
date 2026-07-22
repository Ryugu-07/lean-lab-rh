# H7 Prolate Rayleigh-Gap Preregistration

Date: 2026-07-23

Campaign: `DISCOVERY-20260723-H7-PROLATE-RAYLEIGH-GAP-01`

Selected node: `H7-WEIL-GROUNDSTATE-QUANTITATIVE-APPROX-01`

Status: `IMPLEMENTATION_CI_PASSED / IMMUTABLE_EVIDENCE_REQUIRED`

## Baseline

- `parent_commit`: `cd67e4ad4f899631b11b8d6a8927c5709e4f9fa3`.
- `parent_public_ci`: Lean Action run `29963802981`, build job `89070709361`, passed in `1m57s`.
- `route_selection`: `research/route_selection_post_h14_20260723.md`.
- `nearest_attempts`: H7 M0 alignment, finite matrix/parity, and finite Herglotz campaigns.
- `material_difference`: quantitative projective convergence from Rayleigh excess divided by a
  spectral gap; no continuation of the finite Herglotz scalar-bound optimization.
- `global_goal`: active.

## Locked sources

1. Connes--van Suijlekom, arXiv:2511.23257.
   <https://arxiv.org/abs/2511.23257>
2. Connes--Consani--Moscovici, arXiv:2511.22755, especially Sections 7-8.
   <https://arxiv.org/abs/2511.22755>
3. Connes, arXiv:2602.04022, especially Fact 6.4 and Section 6.6.
   <https://arxiv.org/abs/2602.04022>

The sources identify the true ground-state/prolate comparison but do not state the Rayleigh-gap
ratio below. It is an original candidate and is unavailable as a premise.

## Exact candidate statement

For normalized vectors `xi` and `kappa` in a finite real Euclidean space, a symmetric matrix `A`,
a ground eigenvalue `mu`, and `delta > 0`, assume

```text
A*xi = mu*xi
forall y, <xi,y> = 0 ->
  delta*<y,y> <= <y,A*y> - mu*<y,y>.
```

Define

```text
projectiveDefect xi kappa = 1 - <xi,kappa>^2
rayleighExcess A mu kappa = <kappa,A*kappa> - mu.
```

The finite consumer target is

```text
delta * projectiveDefect xi kappa <= rayleighExcess A mu kappa.
```

The concrete source conjecture replaces `A`, `xi`, and `kappa` by the exact finite-prime Weil
matrix, its normalized ground vector, and the normalized prolate coefficient vector, and asserts
that `rayleighExcess/delta -> 0` in the source-prescribed two-parameter limit.

## Fixed Lean endpoint

Only after this preregistration passes public CI, create
`LeanLab/Riemann/WeilGroundStateRayleighGap.lean` and compile the following without placeholders
or resource relaxation:

1. Define projective defect and Rayleigh excess for finite real vectors.
2. Define a quantitative ground-state gap certificate containing symmetry, normalization, the
   ground eigen-equation, positive gap, and the orthogonal-complement lower bound.
3. Prove the exact projection decomposition
   `kappa = <xi,kappa>*xi + orthogonalRemainder` and orthogonality of the remainder.
4. Prove the Rayleigh excess equals the remainder's quadratic defect.
5. Prove the registered gap-times-projective-defect inequality for normalized `kappa`.
6. Prove the division form when `delta > 0` and a sequence-level consumer showing that a ratio
   tending to zero forces projective defect to zero.
7. Construct a two-dimensional collapsing-gap family with Rayleigh excess tending to zero but
   projective defect identically one; prove all claims in Lean.
8. Register one proven generic consumer Target and one open concrete H7 source-ratio Target, exact
   TargetChecks, and selected axiom prints.

Names may change to fit Mathlib APIs, but the normalized projective defect, positive quantitative
gap, exact Rayleigh excess, ratio consumer, and collapsing-gap witness may not be weakened.

## Source-object boundary

The current H7 matrix API accepts arbitrary diagonal and divided-difference samples. It does not
yet define the actual prime, archimedean, pole, or prolate coefficient data. This campaign must
record that boundary explicitly. A generic theorem cannot be labeled proof of the concrete source
ratio, ground-state convergence, or RH.

No later theorem may assume the source ratio conjecture. A follow-up source-instantiation campaign
requires a separate preregistration and exact formulas for all arithmetic matrix entries and the
prolate vector.

## Success and falsification criteria

- `FULL_SUCCESS_AT_GENERIC_ENDPOINT`: all fixed finite and sequence consumers compile, the
  collapsing-gap witness compiles, and all kernel gates pass.
- `MEANINGFUL_PARTIAL`: the finite quantitative inequality compiles but a precise missing Mathlib
  topology or finite-dimensional API blocks the sequence consumer.
- `CANDIDATE_REJECTED`: an exact source-aligned numerical reconstruction shows the ratio does not
  decrease in a stable cutoff regime, or Lean falsifies one of the proposed generic implications.
- `NO_PROGRESS`: the project cannot state the quantitative certificate without replacing the
  source object by a materially different one.

No success class changes the RH frontier unless an actual source instantiation and all downstream
analytic limits are separately proved.

## Mechanical gates

Before proof-source editing, publish this preregistration with the H14 final public coordinates and
require public Lean Action CI. Keep the six inherited protected files untouched and unstaged.

Before accepting any theorem, require exact Targets and TargetChecks, selected transitive axiom
prints, an empty production forbidden scan, direct compiles, `git diff --check`, full build, and
independent public CI.

## Stop and successor rule

Stop this local campaign at one registered outcome. On success, route selection must decide
whether the concrete arithmetic/prolate source instantiation has enough evidence to justify its
cost. On failure, record the exact obstruction and compare H1 sparse-exception, H2 bow-amplifier,
direct Weil/Li/closure, and other conjecture-pool nodes. Persistent RH Goal remains active.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: inherited-summary recovery was used earlier in the H14 campaign; H14 public
  closure, H7 alignment, finite matrix, Herglotz records, and the three locked primary sources
  were re-read before this selection.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.

## Preregistration public gate

- `commit`: `38d57244841b2afec22a77b4ffeb07ce51db018a`.
- `public_ci`: Lean Action run `29964304967`, build job `89072278256`, passed in `1m37s`.
- `effect`: the fixed proof-source endpoint opened before
  `LeanLab/Riemann/WeilGroundStateRayleighGap.lean` was created.

## Local endpoint result

The generic consumer, ratio form, abstract sequence squeeze, and exact collapsing-gap witness now
compile. This is `FULL_SUCCESS_AT_GENERIC_ENDPOINT` locally. The production scan is empty and the
full `8,750`-job build passes; public implementation CI remains. The concrete
arithmetic/prolate source ratio is still open and has no `leanName`.

Frozen implementation commit `4404a93e92777c904563cda68120e9a1057e084e` passed public Lean
Action run `29965379529`, build job `89075616914`, in `2m36s`. Lean proof source is frozen;
immutable evidence and its own public CI are the next gate. The source ratio remains open.
