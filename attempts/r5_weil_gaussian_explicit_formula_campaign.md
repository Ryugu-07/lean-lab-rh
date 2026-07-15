# R5 Weil Gaussian Arithmetic Explicit-Formula Campaign

Campaign: `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-EXPLICIT-FORMULA-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | Rebuilt the frontier after public closure of the fixed Gaussian zero-side height limit. The adjacent missing edge was arithmetic evaluation of the same right-line integral. | Search only candidates that cross the full zero/pole/Gamma/prime endpoint. |
| 2 | `CONJECTURE_GENERATION` | Screened six candidates: the full fixed-Gaussian formula, integrability only, generic `A_delta`, finite Guinand-Weil Galerkin, the screw operator, and Gaussian positivity. | Send all candidates to strength and carrier audit. |
| 3 | `ADVERSARIAL_TEST` | Generic decay remained absent; finite Galerkin used a different carrier; the screw limit was conjectural; positivity had no off-line mechanism; integrability alone was too narrow. | Select and preregister the full fixed-Gaussian arithmetic formula. |
| 4 | `PROOF_ATTEMPT_A` | Proved the exact vertical Gaussian and L-series forms; evaluated every positive-index term by `integral_cexp_quadratic`; handled `n=0` separately; proved summable integral norms from von-Mangoldt L-series absolute convergence; exchanged sum and integral; derived `logDeriv GammaR = -log(pi)/2 + digamma(s/2)/2`; proved GammaR integrability. | Continue the same proof DAG to the pole pair and final splice. |
| 5 | `PROOF_ATTEMPT_A_CONTINUED` | Built an independent two-pole symmetric rectangle, checked both residues `G_a(0)=G_a(1)=exp(a/4)`, proved top-edge decay and full-line pole value `2*pi*exp(a/4)`, then passed all arithmetic truncations to the full line and proved `gaussianXi_arithmetic_explicit_formula`. | Admit the indivisible endpoint to independent audit; no Attempt B or pivot was needed. |
| 6 | `INDEPENDENT_AUDIT` | Exact TargetChecks and five selected axiom prints pass; all new prints use only `propext`, `Classical.choice`, and `Quot.sound`. The standalone module is warning-free; forbidden-token, declaration, and resource-option scans are empty; `git diff --check` and the 8,670-job full build pass. | Close locally as `BRIDGE_REDUCED`; publish and require public CI before public closure. |
| 7 | `PUBLIC_IMPLEMENTATION_GATE` | Implementation commit `6c65019d9de2d31127dd3bf8389994207c17dcb5` passed public Lean Action CI run `29441160498`, build job `87440149741`, in `2m33s`. | Backfill immutable evidence and require that commit's own public CI before closure. |

## Fixed Endpoint

For every `a>0` and `c>1`, Lean proves

```text
pi * sum_rho exp(a*(rho-1/2)^2)
  = 2*pi*exp(a/4)
      + integral_R G_a(c+iy) * logDeriv GammaR(c+iy) dy
      - sum_n sqrt(pi/a)*Lambda(n)
          * exp(-log(n)/2-log(n)^2/(4a)).
```

The zero sum retains analytic multiplicity through `RiemannXiDivisorZeroIndex`; the arithmetic sum
uses `vonMangoldt`, hence includes every prime power.

## Failed Or Repaired Attempts

- The first complex Gaussian expansion needed an explicit `I^2=-1` normalization.
- The initial exponential product rewrite used the wrong associativity normal form; exposing
  `Lambda(n) * (exp A * exp B)` repaired it without changing the formula.
- Direct type inference for `logDeriv_comp`, `HasSum.congr`, and selected interval limits chose
  unintended implicit arguments; named functions and explicit target types repaired each case.
- The pole evaluation did not use an assumed inverse-Laplace formula. It pivoted within Attempt A
  to the already verified weighted Cauchy-kernel rectangle theorem, with all four edge-avoidance
  conditions proved explicitly.

## Accounting

- `classification`: `BRIDGE_REDUCED`
- `hard_gap_before`: fixed Gaussian zero-side height limit complete; arithmetic evaluation open
- `hard_gap_after`: one complete unconditional fixed-Gaussian explicit formula
- `hard_gap_delta`: 1 fixed-test arithmetic W1c subedge; 0 for RH
- `unconditional_RH_progress`: none
- `remaining_frontier`: generic test-class extension, singular/distributional regularization, W2
  positivity, and RH
- `new_axioms`: none beyond `propext`, `Classical.choice`, and `Quot.sound`
