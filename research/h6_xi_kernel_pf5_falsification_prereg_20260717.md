# H6 Actual Xi-Kernel PF5 Falsification Preregistration

Date: 2026-07-17

Campaign: `FALSIFICATION-20260717-H6-XI-KERNEL-PF5-01`

Mode: `FALSIFICATION`

Status: `PREREGISTRATION_PENDING_PUBLIC_CI`

## Source lock

- Wojciech Michałowski, *On the Pólya Frequency Order of the de Bruijn--Newman Kernel: Certified
  Failure at Order Five and the Toeplitz Threshold Phenomenon*, arXiv:2602.20313 (2026).
- External certificate repository:
  `https://github.com/ScypyonX/pf5-dbn-kernel-certificates`, pinned commit
  `675058772f2ba4bf409d114b6082ac9990b78b34`.
- The exact kernel normalization agrees with the already compiled `deBruijnNewmanPhi`.
- The source is an unreviewed preprint and its `mpmath.iv` result is target-selection evidence
  only. No floating-point or external interval assertion is imported into Lean.

## Exact mathematical target

Define the even physical kernel

```text
K(u) = Phi(abs u).
```

For `i,j in {0,1,2,3,4}`, define

```text
M_ij = K(1/100 + ((i:Real)-(j:Real))/20).
```

Prove using the actual infinite Xi-kernel series that

```text
det(M) < 0.
```

Define `PF5(K)` source-faithfully: every determinant of order `r<=5` formed from strictly
increasing real tuples `x` and `y`, with entries `K(x_i-y_j)`, is nonnegative. Use

```text
x_i = 1/200 + i/20,
y_j = -1/200 + j/20
```

to prove `not PF5(K)`.

## Proposed Lean endpoint

Module: `LeanLab/Riemann/XiKernelPF5Falsification.lean`

```lean
def deBruijnNewmanEvenKernel (u : Real) : Real :=
  deBruijnNewmanPhi |u|

def IsPolyaFrequencyFive (K : Real -> Real) : Prop :=
  forall (r : Nat), r <= 5 ->
    forall x y : Fin r -> Real,
      StrictMono x -> StrictMono y ->
        0 <= Matrix.det (fun i j => K (x i - y j))

def xiKernelPF5ToeplitzMatrix : Matrix (Fin 5) (Fin 5) Real :=
  fun i j => deBruijnNewmanEvenKernel
    (1 / 100 + ((i.1 : Real) - (j.1 : Real)) / 20)

theorem xiKernelPF5ToeplitzMatrix_det_neg :
    Matrix.det xiKernelPF5ToeplitzMatrix < 0

theorem not_isPolyaFrequencyFive_deBruijnNewmanEvenKernel :
    not (IsPolyaFrequencyFive deBruijnNewmanEvenKernel)
```

The final spelling may change to match Mathlib's matrix and monotonicity APIs, but the quantified
mathematical content may not be weakened.

## Fixed proof architecture

1. Prove a reusable rational enclosure theorem for `Real.exp x` from `Real.exp_bound`, splitting
   large rational arguments into powers of arguments of absolute value at most one.
2. For the nine rational arguments
   `1/100 + k/20`, `-4<=k<=4`, bound the first few exact Xi-kernel summands by rational intervals.
   Prove an explicit geometric majorant for the complete omitted `tsum` tail.
3. Package the nine full-kernel enclosures at a width small enough to preserve the determinant
   sign. Decimal values from the source may guide the rational centers but cannot justify them.
4. Evaluate the determinant of the rational center matrix in Lean. Bound determinant perturbation
   through the Leibniz formula or a proved multilinear Lipschitz estimate.
5. Construct the two strictly increasing witness tuples and derive the source-faithful PF5
   negation from the exact negative determinant.

The source's `N=50` truncation is not mandatory. A shorter certified truncation is permitted if
the entire remaining infinite tail is bounded in Lean.

## Success and falsification criteria

Success requires all of the following:

- the nine entry bounds refer to `deBruijnNewmanPhi`, not a finite helper approximation;
- `xiKernelPF5ToeplitzMatrix_det_neg` compiles with the exact rational configuration;
- the strictly increasing witness tuples compile and yield the full `not PF5` endpoint;
- exact TargetChecks and selected transitive axiom prints pass;
- forbidden-token scans, `git diff --check`, standalone compilation, full build, and public CI
  pass.

Falsification of the external claim means Lean proves the exact determinant nonnegative, or a
certified normalization/order audit shows that the cited matrix is not the source matrix. Failure
to obtain sufficiently tight rational bounds is not falsification; it closes only as an OBS node
stating the first exact missing enclosure or Mathlib capability.

Do not report a negative rational-center determinant, a Python interval result, a finite partial
sum, or an abstract implication lemma as campaign success.

## DAG and strength

- DAG position: obstruction branch below H6 physical-kernel total positivity, adjacent to H6-X6
  and below H6-E/G8
- relation to RH: neither direction; it blocks only PF5/PF-infinity physical-kernel strategies
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open
- expected `hard_gap_delta`: 0
- expected `route_infrastructure_delta`: 1
- expected `obstruction_map_delta`: 1
- expected full-success classification: `ACTUAL_KERNEL_PF5_FORMALLY_FALSIFIED`

## Nearest attempts and material difference

- `LITERATURE-20260717-H6-XI-KERNEL-TP2-01` proves actual strict TP2. This campaign tests the first
  sourced finite-order failure beyond that positive result.
- `FALSIFICATION-20260717-H6-XI-LOGCONCAVITY-LEAN-01` rejected an external Lean certificate by
  inspecting vacuous predicates and false axioms. This campaign instead proves a nontrivial
  analytic statement about the actual infinite theta kernel.
- The external PF5 script is reproducible but not kernel-checked. The material new content is a
  Lean-native transcendental and infinite-tail certificate.

## Stop boundary

After the exact negative determinant and `not PF5` theorem are audited, stop. Do not infer global
PF4, a Gaussian-deformation threshold, H6-E, or RH. Return the persistent Goal to value-ranked
route selection.
