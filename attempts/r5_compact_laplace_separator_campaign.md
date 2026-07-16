# R5 Compact Laplace Separator Campaign

Campaign: `CAMPAIGN-20260716-R5-COMPACT-LAPLACE-SEPARATOR-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

Mode: `LITERATURE`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap; campaign bounded by the fixed
  preregistered endpoint
- `compaction_since_previous_campaign`: no

## Normalized Tuple

- `statement`: every selected xi divisor value admits a smooth compact-support log-Laplace test
  normalized to one there with arbitrarily small absolute `tsum` on all different divisor values
- `assumptions`: standard Mathlib bump/convolution analysis, the compiled xi strip and
  reciprocal-square divisor summability, and the compiled finite exponential separator
- `strategy`: normalized modulated bump, inverse-square Laplace decay, finite superlevel
  annihilation, then compact convolution-power suppression
- `unresolved_frontier`: exact physical Laplace/convolution identities and the complete strict
  divisor-tail construction in Lean

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | W2g2 is publicly closed and does not supply an unconditional sign. G3/M2 was historically unselected (open under V4.1). The honest active frontiers are generic W1 compact-support/distributional infrastructure and unconditional W2. | Rotate to a source-focused LITERATURE campaign rather than reopen Gaussian width compression. |
| 2 | `SOURCE_AUDIT` | Connes--Consani Appendix C records the compact-support Weil criterion and a Yoshida separator with finite Mellin zeros, protected target value, and quadratic zero-tail decay. Their main archimedean operator theorem is not a bounded Lean target because its spectral estimate is heavily computer-assisted. | Isolate the compact-support separator mechanism as the candidate source edge. |
| 3 | `LIBRARY_AUDIT` | Mathlib supplies strictly positive smooth compact bumps, compact-support preservation under derivatives and convolution, smoothness of convolution, and whole-line integration by parts. The project supplies the xi strip, reciprocal-square divisor summability, and finite real-shift exponential separation. | The source edge has a plausible no-placeholder Lean path. |
| 4 | `ADVERSARIAL_TEST_AND_ADMISSION` | The naive finite-tail argument is circular because the annihilating polynomial grows with the finite set. The repaired mechanism fixes a transform superlevel, annihilates it once, and uses convolution powers to suppress the remaining values geometrically. Multiplicity copies are explicitly protected. | Admit the exact compact-support `ell^1` xi-divisor separator and begin Proof Attempt A. |
| 5 | `PROOF_A_PHYSICAL_IDENTITIES` | `compactLaplaceTransform` compiles with honest weighted-kernel integrability, real-translation covariance, additive-convolution factorization, and onefold/twofold integration by parts. | Continue: the physical transform infrastructure is sound. |
| 6 | `PROOF_A_DIVISOR_SUMMABILITY` | Two integrations by parts give a closed-strip inverse-square bound controlled by `compactLaplaceSecondDerivativeMass`; the existing reciprocal-square xi-divisor theorem yields complete multiplicity-bearing absolute summability. | Close proof DAG step 3. |
| 7 | `PROOF_A_BASE_AND_SUPERLEVEL` | A fixed unit-integral smooth bump modulated by `exp(-rho0*x)` has transform exactly one at `rho0`; summability makes every positive transform superlevel finite after excluding the full equal-value class. | Continue with one fixed threshold `q=1/2`. |
| 8 | `PROOF_A_FINITE_ANNIHILATOR` | A positive real shift separates the target exponential from the finite unwanted value set. A normalized complex polynomial vanishes on all bad values, and its coefficient packet is realized by finitely many real translates with exact Laplace covariance, smoothness, and compact support. | Close proof DAG step 5 without circular tail enlargement. |
| 9 | `PROOF_A_CONVOLUTION_SUPPRESSION` | The `(m+1)`-fold compact convolution iterate has transform `F^(m+1)`. The normalized packet tail is pointwise bounded by `B*2^(-m)*abs(F)`, so complete-divisor `tsum` comparison and geometric convergence select an `m` with strict tail below any positive epsilon. | Exact preregistered endpoint compiles. |
| 10 | `LOCAL_AUDIT` | Formal module, exact Targets and TargetChecks compile. Five selected transitive axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden/scratch/resource scans and `git diff --check` are clean; the full 8,678-job build passes. | Local gate passed; publish the implementation and require independent public CI. |
| 11 | `IMPLEMENTATION_PUBLIC_CI` | Implementation commit `6d12bad98b80c34217757df01943509965a64781` passed public Lean Action CI run `29461298466`, build job `87505125618`, in `1m47s`. | Backfill immutable evidence, publish it, and require the evidence commit's own CI before closure. |
| 12 | `PUBLIC_CI_EVIDENCE_AND_CLOSURE` | Evidence commit `941756c2e7e0b4da8f765dc7187e4be703af36c8` passed public Lean Action CI run `29461494669`, build job `87505716647`, in `2m22s`. The implementation and its evidence are independently public-built. | Close this fixed endpoint and return the active RH Goal to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`. |

## Current Accounting

- `hard_gap_before`: G6/W1 open; G7/W2 open; G3/M2 historically unselected (open under V4.1)
- `hard_gap_after`: G6/W1 remains open with one compact-support reverse-separation subedge compiled; G7/W2 and G3/M2 remain unchanged
- `hard_gap_delta`: 0
- `classification`: `KNOWN_MECHANISM_RECONSTRUCTED` / unconditional W1 reverse-separation component
- `next_gate`: fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; do not reopen this separator endpoint
  without a strictly stronger target

## Compiled Endpoint

The formal module is `LeanLab/Riemann/WeilCompactLaplaceSeparator.lean` (699 lines). Its exact
endpoint is `exists_compactSupport_xiDivisor_laplace_tsum_separator`. The proof protects every
multiplicity copy with the selected zero value, uses no RH premise, and contains no placeholder or
project axiom. It does not prove a generic explicit formula, unconditional Weil positivity, G7,
or RH.
