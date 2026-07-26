# H9 Riesz Mellin Boundary

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-RIESZ-MELLIN-BOUNDARY-01`

Selected node: `H9-RIESZ-EXPONENTIAL-MELLIN-BOUNDARY-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / FALSIFICATION`.
- `exact_target`: compile the actual `k=2` Riesz Mobius-exponential kernel, its zero value,
  the ordinary Mellin identity on `-1/2<Re(s)<0`, a divergence witness inside the wider
  published literal region, and the conditional holomorphic Mellin extension supplied by an
  explicit power-decay hypothesis.
- `relation_to_RH`: the still-unproved decay
  `P_2(x)=O_epsilon(x^(-3/4+epsilon))` is equivalent to RH. This campaign does not assume or
  prove that decay and does not yet continue the product identity into the zero-free strip.
- `success`: exact base-strip identity, exact zero-end nonconvergence, conditional extension,
  M0 definition alignment, standard-only axiom audit, full build, and public evidence gates.
- `falsification`: reject literal-integral use beyond convergence, a hidden `k=1` substitution,
  an incorrect sign or Dirichlet exponent, or zeta division below its proved nonvanishing
  half-plane.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the H9 Redheffer characteristic-polynomial endpoint. | Final ledger `2799ec66850919db744026ae58aaea4c2bd2f769` passed run `30210035283`, job `89814585909`, in `1m37s`. | Return to fresh cross-family route selection. |
| `CROSS_FAMILY_AUDIT` | Rechecked the first open edges in H0/H1/H2/H7/H8/H9/H10/H11/H12. | The live frontier candidates require a new global analytic, spectral, geometric, or sparse-exception input; immediate Redheffer continuation would stay in the same branch. | Search for a missing historical arithmetic-analytic route. |
| `LAGARIAS_REFINEMENT_AUDIT` | Compared MacArevey's 2026 monotone Lagarias auxiliary and superabundant least-counterexample theorem with Lagarias 2001. | Lagarias already gives a colossally abundant counterexample if the inequality fails, a thinner class than superabundant numbers. | Do not select the refinement as a shorter RH edge. |
| `Riesz_SOURCE_AUDIT` | Read Riesz 1916 metadata and Agarwal--Garg--Maji 2022 equations `(1.5)`, Lemma 2.4, and `(3.31)`. | The `k=2` kernel is absolutely convergent and RH-equivalent decay is explicit. Lemma 2.4's displayed ordinary-integral region includes `Re(s)>=0`, although `P_2(0)=1/zeta(2)!=0`. | Select a literal-integral versus analytic-continuation boundary campaign. |
| `REPOSITORY_DUPLICATION_SCAN` | Searched production, research, attempts, and handoff files for the actual Riesz Mobius-exponential kernel. | The repository has general dilation-system Riesz references and Mellin infrastructure, but no `P_2`, no exponential Mobius kernel, and no Riesz Mellin criterion. | Admit the new H9 subroute. |
| `LEAN_API_SURVEY` | Checked `hasSum_mellin`, Gamma integral APIs, Mobius L-series summability, reciprocal zeta, rpow integrability, and Mellin big-O holomorphy. | The base identity, zero-end divergence, and conditional extension have a direct no-sorry API path. The subsequent product-identity continuation remains a separate complex-analytic edge. | Publish docs-only preregistration before proof edits. |
| `PUBLIC_PREREG_GATE` | Published the docs-only fixed endpoint. | Commit `2a0f1dbbb894f107b5a4c4c8a5e9f1f5837a9811` passed run `30210947076`, job `89816945706`, in `1m37s`. | Open production editing. |
| `KERNEL_AND_ZERO` | Defined the actual Mobius coefficient, `n^-2` frequency, exponential term, and tsum kernel; proved summability, continuity, local integrability, and the exact zero value. | `P_2(0)=1/zeta(2)!=0` compiles from the existing Mobius L-series identity. | Normalize the Mellin sum. |
| `BASE_STRIP_IDENTITY` | Proved the real-rpow and complex-cpow coefficient transformations and applied Mathlib's `hasSum_mellin`. | Ordinary convergence and `zeta(2*s+2) M[P_2](-s)=Gamma(-s)` compile on `-1/2<Re(s)<0`; zeta nonvanishing is used only at `Re(2*s+2)>1`. | Audit the displayed right-side point. |
| `DISPLAYED_POINT_FALSIFICATION` | Used right continuity and `P_2(0)!=0` to dominate `x^-3/2` near zero. | `¬ MellinConvergent P_2 (-1/2)` compiles by `integrableOn_Ioo_rpow_iff`. | Add the conditional decay interface. |
| `DECAY_INTERFACE` | Proved `P_2=O(x^-a)` unconditionally for every `0<=a<1/2`, then exposed general explicit `O(x^-a)` consumers. | Base-strip convergence is unconditional; arbitrary-decay convergence and Mellin differentiability compile on `-a<Re(s)<0`. The RH-equivalent `a=3/4-epsilon` decay is not proved. | Register Target and audits. |
| `LOCAL_GATES` | Added one aggregate Target, four exact TargetChecks, and eight selected axiom prints; ran standalone compilation, forbidden scan, diff check, and full build. | New-module scan empty; selected axioms standard only; full build `8773/8773`. | Freeze and publish implementation. |
| `IMPLEMENTATION_PUBLIC_CI` | Froze and pushed the complete implementation and local ledgers. | Commit `096aea939d27fb6828b702296c156bbef4ba1559` passed run `30212146718`, job `89820083261`, in `2m25s`. | Freeze all `LeanLab/` files and publish docs-only immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC_CI` | Published docs-only proof-freeze evidence. | Commit `5448bd74cdf55a8ead8847f6c7cd50e21e8711e7` passed run `30212403937`, job `89820745802`, in `1m39s`; the implementation-to-evidence `LeanLab/` diff is empty. | Publish one docs-only final ledger and require public CI. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state, then rechecked governance, current
  route ledgers, the Redheffer public closure, protected worktree state, primary-source text,
  repository duplication, and pinned Mathlib APIs.
- `global_goal`: active.

## Assumption frontier

The unconditional endpoint may use only absolute Mobius L-series convergence at real part
greater than one, Euler's Gamma integral, justified sum-integral interchange, continuity and
power-integrability facts, and the existing standard zeta/Gamma/Mellin definitions.

The extension theorem may take an explicit `IsBigO` decay hypothesis as an argument. It may not
instantiate that hypothesis with exponent `3/4-epsilon`, assume RH, assume zeta zero-freeness in
the critical strip, or identify an analytic continuation with a divergent ordinary integral.

The six inherited user/exposure files remain untouched and unstaged.

## Local result

- `result`: `RIESZ_TWO_MELLIN_LITERAL_STRIP_CORRECTED`.
- `module`: `LeanLab/Riemann/RieszMellinBoundary.lean`, 490 lines.
- `proved_boundary`: the literal ordinary-integral strip is `-1/2<Re(s)<0`; the displayed
  source point `s=1/2` gives Mellin argument `-1/2` and diverges at zero.
- `criterion_status`: the source's analytic-continuation argument may still begin from the
  corrected base strip. No Riesz decay, critical-strip zero-free theorem, or RH proof follows.
- `frozen_implementation`: `096aea939d27fb6828b702296c156bbef4ba1559`, public-green.
- `immutable_evidence`: `5448bd74cdf55a8ead8847f6c7cd50e21e8711e7`, public-green.
- `next_gate`: docs-only final ledger and public Lean Action CI.
- `global_goal`: active.
