# H6 Xi-Kernel Log-Concavity External Lean Audit

Campaign: `FALSIFICATION-20260717-H6-XI-LOGCONCAVITY-LEAN-01`

Mode: `FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_CI_PASSED_EVIDENCE_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited continuation; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, H6 route card, current route portfolio, and the closed H6-X4 attempt
  were reread before selection
- `global_goal`: active

## Selection record

- `exact_target`: kernel-check a counterexample to the pinned external repository's exact
  no-convergence Hurwitz schema and prove that its formal log-concavity predicate is vacuous
- `source_commit`: `7a89db1d546257d8dabefe1ac8b8d4769298a355`
- `material_difference`: audit a claimed theta-specific Lean certificate rather than extend finite
  heat-Li values or reuse a generic positive-kernel model
- `nearest_attempt`: H6-X4 all-index criterion and `OBS-H6-POSITIVE-COSH-LI3-01`
- `assumption_frontier_before`: actual Xi-kernel TP2 is not compiled in this project; TP2 does not
  imply TP-infinity or RH; H6-E/G8 remains the all-real-zero endpoint
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open

## Pre-proof findings

- v2 paper scope correctly says TP2 is necessary but insufficient for RH
- external README retains the obsolete TP2-implies-real-zeros claim
- external `IsLogConcaveOn` concludes `True`
- external Hurwitz axiom omits analyticity and every convergence hypothesis
- advertised full-kernel Lean theorems conclude only `True`
- decisive perturbation claims are custom axioms of type `True`
- Python verification omits the `n>=6` tail and the global Region-B decrease proof
- repository contains no `LICENSE` file; no code is copied

## Pending gates

- preregistration commit, push, and public Lean Action CI: passed
- exact Lean countermodel and aggregate endpoint: passed locally
- Targets, TargetChecks, AxiomsAudit, scans, and full build: passed locally
- implementation public CI: passed
- evidence backfill commit and public CI: pending
- final public closure log update: pending

## Public implementation evidence

- implementation commit `8ecb002d1591ae93fbc23ba42c7a487c16c8beb5`
- public Lean Action CI run `29550587517`, build job `87792042425`, passed in `1m50s`

## Current result

- `result`: `EXTERNAL_FORMALIZATION_REJECTED_AS_PREMISE_PUBLIC_IMPLEMENTATION`
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 0
- `proof_source_edits`: `LeanLab/Riemann/XiKernelLogConcavityAudit.lean`

## Loop record: exact formal counterexample

1. The preregistration commit `def8b00d309ef5acc6a0f44a7eb0b47c0db25b01` passed public Lean
   Action CI run `29549982781`, build job `87790283637`, in `1m32s` before proof edits.
2. The source was pinned again at `7a89db1d546257d8dabefe1ac8b8d4769298a355`. A complete scan
   finds thirteen explicit custom `axiom` declarations across `Basic.lean`, `ExpBound.lean`,
   `Analytic.lean`, and `Polya.lean`.
3. Lean proves every constant function `F_n(z)=1` has only real zeros vacuously, while
   `G(z)=z-i` is nonzero at `0` and has the nonreal zero `i`.
4. These witnesses refute the exact external Hurwitz proposition, which has neither analyticity
   nor compact-uniform convergence among its premises.
5. Lean separately proves the exact reconstructed `IsLogConcaveOn` shape for every real function,
   because its conclusion is only `True`.
6. `xiKernelLogConcavityExternalAudit_endpoint` bundles the vacuous predicate, both witness facts,
   the nonreal-zero conclusion, and the schema negation.

## Mechanical audit

- standalone new-module compile: diagnostic-free
- dedicated Lake build: 782 jobs, success
- exact Targets and TargetChecks: diagnostic-free
- selected axiom prints: only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden placeholder/declaration/resource scans: empty
- full build: 8,697 jobs, success
- `git diff --check`: pass
- implementation public CI: run `29550587517`, build job `87792042425`, passed in `1m50s`
- immutable evidence closure: pending

## Assumption frontier

The campaign rejects only the pinned external machine-verification chain. It does not prove the
full kernel is not log-concave, and it does not challenge the v2 paper's corrected statement that
TP2 is weaker than TP-infinity. A future proof of actual Xi-kernel log-concavity needs a real
`Phi`, derivative definitions, a complete infinite-tail estimate, and no custom axioms. H6-E/G8,
W2/G7, M2/G3, and RH remain open.
