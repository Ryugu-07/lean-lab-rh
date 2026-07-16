# R5 Compact Weil Arithmetic Formula Campaign

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

Mode: `DISCOVERY -> PROOF_ATTEMPT_A`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap; campaign bounded by the fixed
  complete compact-smooth arithmetic explicit-formula endpoint
- `compaction_since_previous_campaign`: yes; proof work resumed from the preserved campaign
  summary and rechecked the live Goal, repository state, fixed statement, and current Lean module

## Fixed-Gap Record

- `node_id`: W1
- `gap_id`: G6
- `work_class`: FORMALIZATION
- `result_class`: `BRIDGE_REDUCED`
- `assumption_frontier_before`: the reflection-symmetrized compact-smooth class has a complete
  zero-side cutoff, but its right-line pole, GammaR, and von-Mangoldt evaluation are external
- `assumption_frontier_after`: exact prime inversion and interchange, finite physical support,
  pole convergence and residues, GammaR integrability, and the full arithmetic identity all follow
  from only `hf`, `hfsupp`, and `hc`
- `hard_gap_before`: W1c1 is open on the compact arithmetic side
- `hard_gap_after`: the complete compact-smooth reflection-class explicit formula is compiled;
  quotient/completeness, distributional regularization, W2/G7, and RH remain open
- `expected_hard_gap_delta`: 1 at the W1c1 compact arithmetic subedge
- `preregistration_commit_sha`: `ccebc64b1f3419636461e6fbf968fc55c4f24b8c`
- `commit_sha`: `55a6406f235a7548bf7f7d53ae5d30014795e9ce`
- `evidence_commit_sha`: `ed5d03f65bd234f95afb55389b2766d611a3eeab`

## Normalized Tuple

- `statement`: every smooth compactly supported additive-log function satisfies the complete
  reflection-symmetrized xi explicit formula with an explicit finite physical von-Mangoldt side
- `assumptions`: `ContDiff R infinity f`, `HasCompactSupport f`, and `1<c`
- `strategy`: Schwartz Fourier inversion with exact `2*pi` scaling, right-half-plane L-series
  interchange, compact sixth-order decay, the compiled generic pole residue skeleton, and GammaR
  logarithmic growth
- `unresolved_frontier`: quotient/completeness and continuity for the full admissible test class,
  distributional regularization, unconditional W2/G7 positivity, and RH

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `INDEPENDENT_AUDIT -> ROUTE_SELECTION` | The compact zero-side campaign is publicly closed with preregistration, implementation, evidence, and closure CI. W1c1 now has one remaining compact arithmetic subedge; W2/G7 and parked G3/M2 remain open. | Rotate from LITERATURE to DISCOVERY and test whether current Fourier, contour, and decay interfaces suffice for the complete compact arithmetic formula. |
| 2 | `DISCOVERY_INTERFACE_AUDIT` | Mathlib converts `C_c^infinity` functions directly to Schwartz maps and supplies pointwise Fourier inversion. The project supplies the generic two-pole rectangle residue identity, selected-height zero limit, sixth-order compact decay, GammaR digamma growth, and absolutely convergent von-Mangoldt L-series for `c>1`. | Screen a full arithmetic endpoint against partial helper and repeated-criterion alternatives. |
| 3 | `FIVE_CANDIDATE_ADVERSARIAL_SCREEN` | Prime inversion alone, pole/Gamma helpers alone, and finite physical support alone are incomplete endpoints. A new compact RH-equivalent positivity criterion repeats the compiled Gaussian separator without an unconditional sign mechanism. The complete compact formula combines all nontrivial interfaces and changes W1c1. | Admit and preregister the quantified complete compact arithmetic formula before any Lean proof edit. |
| 4 | `PROOF_ATTEMPT_A_PRIME_INVERSION` | The compact vertical Laplace branch is the Fourier transform of `exp(c*x)f(x)` at `-y/(2*pi)`. Schwartz inversion and exact scaling give `2*pi*f(log n)` on the first branch and `2*pi*f(-log n)/n` on the reflected branch. Lean handles `n=0` separately and proves absolute series/integral interchange. | Retain the exact preregistered physical weight; advance to its mandatory finite-support proof. |
| 5 | `PROOF_ATTEMPT_A_FINITE_SUPPORT` | Compactness of `tsupport f` bounds every nonzero `f(log n)` or `f(-log n)` argument. Exponentiating the resulting `log n` bound places the natural support inside a finite `Iio N`. | Accept genuine `Function.HasFiniteSupport`; do not substitute mere summability. |
| 6 | `PROOF_ATTEMPT_A_POLES` | Inverse-sixth selected top-edge decay forces the compact pole-pair top integral to zero. The generic two-pole rectangle identity, reflection `F(0)=F(1)`, right-line integrability, and limit uniqueness yield exactly `2*pi*F(1)`. | Pole DAG node discharged without a new premise. |
| 7 | `PROOF_ATTEMPT_A_ARCHIMEDEAN` | A stronger reusable route than the preregistered coarse tail split was available: the Fourier transform of the compact Schwartz density has an integrable first absolute moment. Reflection preserves this bound, which absorbs the compiled linear digamma majorant and proves full-line GammaR integrability. | Archimedean DAG node discharged with no resource relaxation. |
| 8 | `PROOF_ATTEMPT_A_ASSEMBLY` | On every selected finite right edge, Lean splits `logDeriv riemannXi` into pole, GammaR, and von-Mangoldt terms with exact signs. All three truncations converge; uniqueness against the compiled zero-side limit proves the fixed endpoint verbatim. | Accept the indivisible endpoint and advance to independent local audit. |
| 9 | `INDEPENDENT_LOCAL_AUDIT` | The 1,012-line module is diagnostic-free. Exact Targets and TargetChecks compile; five selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; placeholder, declaration, `native_decide`, unsafe, resource-option, and scratch scans are empty; `git diff --check` passes; the full 8,681-job build succeeds. | Classify as `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at the compact W1c1 arithmetic subedge. Publish implementation and require independent public CI. |
| 10 | `PUBLIC_IMPLEMENTATION_CI` | Implementation commit `55a6406f235a7548bf7f7d53ae5d30014795e9ce` passed public Lean Action CI run `29466850965`, build job `87521708037`, in `1m51s`. | Backfill immutable evidence and require the evidence commit's own public CI before closure. |
| 11 | `PUBLIC_CI_CLOSURE` | Evidence commit `ed5d03f65bd234f95afb55389b2766d611a3eeab` passed public Lean Action CI run `29467021669`, build job `87522220122`, in `1m43s`. The preregistration, implementation, and evidence states all independently build. | Close as `BRIDGE_REDUCED` and return the persistent RH Goal to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; do not extend this campaign with helper-only work. |

## Preregistration

The exact statement, source boundary, proof DAG, five-candidate screen, adversarial tests, and
rejection conditions are fixed in
`research/r5_compact_weil_arithmetic_formula_prereg_20260716.md`.

No Lean proof file has been edited for this campaign at preregistration time.

Preregistration commit `ccebc64b1f3419636461e6fbf968fc55c4f24b8c` passed public Lean Action CI
run `29465070647`, build job `87516408926`, in `1m31s`.

## Local Result

The exact endpoint now compiles as
`symmetrizedCompactLaplaceXi_arithmetic_explicit_formula` in
`LeanLab/Riemann/WeilCompactLaplaceArithmeticFormula.lean`. The same module proves the exact
one-term physical prime formula, absolute interchange, genuine finite natural support, the full
pole residue integral, an integrable first absolute moment for the compact vertical weight,
GammaR integrability, and every selected-height arithmetic limit.

No real-valuedness or evenness premise was added. The reflected branch carries exactly `1/n`, the
line parameter cancels, the two pole residues contribute `2*pi*F(1)`, and the complete analytic xi
divisor retains multiplicity.

## Local Verification

- standalone source check: pass with no diagnostics
- Lake module build: pass, 8,646 jobs; replayed warnings are confined to pre-existing modules
- exact `TargetChecks.lean`: pass
- selected transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- placeholder/declaration/`native_decide`/unsafe/resource/scratch scans: empty
- `git diff --check`: pass
- full `lake build`: pass, 8,681 jobs

Local classification is `BRIDGE_REDUCED`. The broad RH Goal stays active; W2/G7, G3/M2,
distributional regularization, and RH are unchanged.

## Public Implementation Verification

Implementation commit `55a6406f235a7548bf7f7d53ae5d30014795e9ce` passed public Lean Action CI
run `29466850965`, build job `87521708037`, in `1m51s`. The exact theorem and all repository
checks therefore rebuild from the public commit. Immutable evidence backfill and its own public CI
remain before campaign closure.

## Public Closure

Evidence commit `ed5d03f65bd234f95afb55389b2766d611a3eeab` passed public Lean Action CI
run `29467021669`, build job `87522220122`, in `1m43s`. Together with preregistration run
`29465070647` and implementation run `29466850965`, the fixed campaign is publicly closed as
`BRIDGE_REDUCED`. The persistent RH Goal remains active and returns to fresh route selection;
quotient/completeness, distributional regularization, W2/G7, G3/M2, and RH remain open.
