# R5 Weil Gaussian Height-Limit Campaign

Campaign: `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-HEIGHT-LIMIT-01`

Date: 2026-07-16

Status: `LOCALLY_CLOSED_BRIDGE_REDUCED_PENDING_PUBLIC_CI`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget; campaign capped by Discovery Protocol V3
- `compaction_since_previous_campaign`: yes

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | Rebuilt the frontier after the q=2 campaign. The generic `A_delta` height limit still lacks vertical decay; W1c1 has only the finite rectangle theorem. | Search for a fixed entire test with intrinsic horizontal decay. |
| 2 | `CONJECTURE_GENERATION` | Screened six normalized candidates spanning generic Weil limits, the symmetric Gaussian, another q-weighted criterion, Li/operator wrappers, spectral compression, and exact approximants. | Send all candidates to strength and counterexample audit. |
| 3 | `ADVERSARIAL_TEST` | Only `G_a(s)=exp(a*(s-1/2)^2)` has route-specific new evidence: exact reflection symmetry and `exp(-a*T^2)` horizontal decay. It is unconditional and weaker than RH. | Select and preregister the fixed Gaussian height limit. |
| 4 | `PROOF_ATTEMPT_A` | Proved the Gaussian algebra, xi log-derivative reflection, absolute multiplicity-bearing Gaussian zero summability, a reciprocal-square-only near-zero count, quantitatively separated selected heights, a zero-free boundary theorem, a fourth-power horizontal log-derivative bound, and convergence of finite Gaussian zero cutoffs. | Continue to the indivisible contour endpoint; helpers alone do not close the campaign. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | Proved uniform Gaussian decay on selected top edges, `Top_n -> 0`, both edge-reflection identities, `Right_n=-i*Top_n+pi*ZeroCutoff_n`, and the fixed existential endpoint `exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral`. | Admit the exact endpoint to independent audit. |
| 6 | `INDEPENDENT_AUDIT` | Rechecked the quantitative height selection, near/far genus-one split, analytic multiplicity, absolute `tsum`, rectangle orientation, factor `pi`, and absence of RH, simplicity, enumeration, or Riemann--von Mangoldt. Standalone compilation is warning-free; exact TargetChecks, five standard-only axiom prints, five empty forbidden scans, `git diff --check`, the module build, and the 8,669-job full build pass. | Close locally as `BRIDGE_REDUCED`; require public implementation CI before public closure. |

## Fixed Endpoint

For every `a>0` and `c>1`, Lean constructs symmetric heights `T_n -> infinity` whose rectangle
boundaries contain no xi zero and proves

```text
integral_{-T_n}^{T_n} G_a(c+iy) * (xi'/xi)(c+iy) dy
  -> pi * sum_rho G_a(rho),
```

where the zero sum is absolutely convergent and indexed by the Hadamard divisor, so analytic
multiplicity is retained.

## Proof Mechanism

- `sum_rho norm(rho)^(-2)<infinity` dominates `sum_rho norm(G_a(rho))`.
- The same reciprocal-square mass bounds the number of zeros of norm at most `R` by `O(R^2)`.
- Finite-union measure avoidance chooses `T` in each unit interval at an explicit distance from
  every nearby absolute zero ordinate.
- Nearby compensated zero terms use the ordinate separation; far terms use genus-one
  reciprocal-square decay. Together with the degree-one Hadamard polynomial, this gives an
  intentionally coarse `O(R^4)` horizontal bound.
- The exact Gaussian norm contributes `exp(-a*T^2)`, which absorbs `R^4`.
- Functional-equation reflection reduces the finite rectangle identity to
  `Right_n=-i*Top_n+pi*ZeroCutoff_n`; the two independently proved limits finish the endpoint.

## Accounting

- `classification`: `BRIDGE_REDUCED`
- `hard_gap_before`: fixed Gaussian W1c1 height limit open after the finite rectangle theorem
- `hard_gap_after`: fixed Gaussian zero-side height limit complete
- `hard_gap_delta`: 1 for this fixed-test W1c1 subedge; 0 for RH
- `unconditional_RH_progress`: none
- `remaining_frontier`: prime/archimedean evaluation for this Gaussian, generic test-class
  extension, W1c2 regularization, W2 positivity, and RH
- `new_axioms`: none beyond `propext`, `Classical.choice`, and `Quot.sound`

The persistent RH Goal remains active. Public implementation and evidence commits are still
required before this campaign is publicly closed.
