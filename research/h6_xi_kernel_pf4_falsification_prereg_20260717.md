# H6 Actual Xi-Kernel Global PF4 Falsification Preregistration

Date: 2026-07-17

Campaign: `FALSIFICATION-20260717-H6-XI-KERNEL-PF4-01`

Mode: `FALSIFICATION`

Status: `PREREGISTRATION_PENDING_PUBLIC_CI`

## Source lock

- Wojciech Michalowski, *On the Polya Frequency Order of the de Bruijn--Newman Kernel: Certified
  Failure at Order Five and the Toeplitz Threshold Phenomenon*, arXiv:2602.20313 (2026).
- The source defines `PF_k` by nonnegative determinants for every order `r <= k` and every pair
  of strictly increasing real tuples. Its global `PF4` question is left open; the positive
  order-four evidence in the source concerns a Toeplitz subfamily only.
- The exact kernel normalization agrees with the compiled `deBruijnNewmanEvenKernel`.
- Numerical output is target-selection evidence only. No floating-point value, external interval,
  optimizer result, or finite truncation may become a Lean premise.

## Exact mathematical target

Define source-faithful order-four Polya frequency by

```text
PF4(K) := for every r <= 4 and strictly increasing x,y : Fin r -> Real,
          det [K(x_i-y_j)] >= 0.
```

Search for explicit rational strictly increasing tuples `x,y : Fin 4 -> Real` for which

```text
det [deBruijnNewmanEvenKernel (x_i-y_j)] < 0.
```

If a candidate is found, prove the determinant inequality for the actual infinite theta-kernel
series and derive `not PF4(deBruijnNewmanEvenKernel)`.

## Proposed Lean endpoint

Module: `LeanLab/Riemann/XiKernelPF4Falsification.lean`

```lean
def IsPolyaFrequencyFour (K : Real -> Real) : Prop :=
  forall (r : Nat), r <= 4 ->
    forall x y : Fin r -> Real,
      StrictMono x -> StrictMono y ->
        0 <= Matrix.det (fun i j => K (x i - y j))

theorem xiKernelPF4WitnessMatrix_det_neg :
    Matrix.det xiKernelPF4WitnessMatrix < 0

theorem not_isPolyaFrequencyFour_deBruijnNewmanEvenKernel :
    not (IsPolyaFrequencyFour deBruijnNewmanEvenKernel)
```

The witness constants and matrix definition remain unfrozen until numerical search selects a
rational candidate. Once proof-source implementation begins, any witness replacement must be
recorded in the attempt log with its determinant margin and reason.

## Fixed search and proof architecture

1. Parameterize global order-four configurations by positive rational gaps for `x` and `y` and
   one relative translation. Search genuinely non-Toeplitz configurations; a Toeplitz-only scan
   cannot settle the target.
2. Evaluate candidates at high precision using the exact kernel formula with an independently
   controlled numerical tail. Rank by a scale-aware determinant margin and then round the best
   candidates to simple rationals.
3. Reuse the compiled rational exponential enclosures and full-`tsum` tail architecture from the
   PF5 campaign. Generate new entry-specific bounds for the finitely many absolute differences in
   the selected `4x4` witness.
4. Prove an exact rational center determinant is negative and a complete determinant perturbation
   bound is smaller than its negative margin.
5. Prove both witness tuples strictly increasing and derive the source-faithful global PF4
   negation.

Numerical search may select a witness but cannot certify one. No finite prefix of the theta series
counts as the physical kernel.

## Success and failure criteria

Success requires all of the following:

- an explicit non-Toeplitz rational witness with compiled strict monotonicity proofs;
- a negative determinant theorem for the actual full `deBruijnNewmanEvenKernel` matrix;
- the quantified `not IsPolyaFrequencyFour deBruijnNewmanEvenKernel` endpoint;
- exact TargetChecks and selected transitive axiom prints;
- forbidden-token scans, `git diff --check`, standalone compilation, full build, and public CI.

A numerical negative determinant is not success. If bounded search finds no robust negative
candidate, close this campaign as `NO_PROGRESS` with the exact parameter families, bounds, sample
counts, optimizer settings, best certified numerical margin, and conditioning caveats. Such a
search does not prove PF4. If a candidate is found but Lean cannot close it, record the first exact
missing enclosure or arithmetic step as an obstacle and do not state a kernel-level result.

## DAG and strength

- DAG position: obstruction branch below H6 physical-kernel total positivity, adjacent to the
  compiled PF5 failure and below H6-E/G8
- relation to RH: neither direction; a counterexample blocks PF4/PF-infinity physical-kernel
  strategies but does not decide H6-E or RH
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open
- expected `hard_gap_delta`: 0
- expected `route_infrastructure_delta`: 0 or 1, depending on whether generic witness tooling is
  compiled
- expected `obstruction_map_delta`: 1 only on a compiled counterexample
- expected full-success classification: `ACTUAL_KERNEL_GLOBAL_PF4_FORMALLY_FALSIFIED`

## Nearest attempts and material difference

- `FALSIFICATION-20260717-H6-XI-KERNEL-PF5-01` proves a negative `5x5` Toeplitz determinant for the
  actual full kernel. It supplies the enclosure infrastructure but says nothing about PF4.
- The source's order-four positive results and computations concern Toeplitz configurations. This
  campaign searches the full seven-parameter configuration space after translation reduction.
- `LITERATURE-20260717-H6-XI-KERNEL-TP2-01` proves actual strict TP2. Order four requires new
  determinants and is not an iteration of that theorem.

## Stop boundary

Stop after either (a) the exact full-kernel PF4 counterexample is publicly audited, or (b) the
preregistered bounded search is exhausted and its strongest candidate or obstruction is logged.
Do not infer PF4 from a failed search, and do not infer H6-E or RH from either outcome. Return the
persistent Goal to value-ranked route selection.
