# G4-F3 Burnol Finite-Dimensional Asymptotics Pre-Registration

Date: 2026-07-14

Batch ID: `BATCH-20260714-G4-F3`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F3`
- `work_class`: `SOURCE_FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: preregistered

Formalize Burnol's complete finite-dimensional asymptotic input as one indivisible batch. The
batch consists of the normalized boundary vectors, every entrywise Gram limit, both target-pairing
limits, nonsingularity and inversion of the limiting Hilbert blocks, and passage of matrix inverse
through the finite Gram limit. A local integral estimate, a generic matrix-continuity lemma, or a
standalone finite-sum identity does not close F3.

## Primary Source

Jean-Francois Burnol, *A lower bound in an approximation problem involving the zeros of the
Riemann zeta function*, arXiv `math/0103058v2`, TeX source SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.

- Source lines 579-623 define `X` and state the Gram limits.
- Source lines 625-645 state and prove the target-pairing limits.
- Source lines 655-670 use finite Gram inversion and the Hilbert/Cauchy inverse entry `m^2`.

## Parameter Domain And Normalization

For `0 < lambda < 1`, put

```text
L(lambda) = log(1/lambda),
X(lambda,s,k) = L(lambda)^(-1/2-k) * Y(lambda,s,k).
```

The asymptotic filter is `nhdsWithin 0 (Ioi 0)`. All critical parameters satisfy
`re(s)=1/2`. Endpoint changes among `(lambda,1)`, `[lambda,1]`, and their half-open variants are
permitted only after proving the corresponding null-set integral equality.

## Exact Scalar Limits

The batch must expose source-facing Lean declarations equivalent to

```text
lim_(lambda -> 0+) inner (X lambda s1 k) (X lambda s2 l)
  = if s1 = s2 then 1/(k+l+1) else 0,

lim_(lambda -> 0+) sqrt(L(lambda)) * inner chi1 (X lambda s k)
  = if k = 0 then (s-1)/s^2 else 0.
```

The Gram proof must consume the explicit F2 representative. On `(lambda,1]`, it must separate
the highest logarithmic term

```text
V(s) * (-log t)^k * t^(-s)
```

from lower derivative terms and the lambda-independent bounded remainder. The tail on
`[1,infinity)` must be controlled by the F2 `(1+abs(log t))^2/t` estimate. For unequal critical
parameters the leading oscillatory moment must be shown to have order at most `L^(k+l)`, not
discarded by an informal cancellation claim.

For the target pairing, the batch must construct and verify the physical representative

```text
V(chi1)(t) = sinc(2*pi*t) - M(sinc(2*pi*t)),
```

prove its required small-`t` decay and large-`t` integrability, and pass the physical cutoff to
zero. Reusing the model-kernel pairing is not a proof of this target limit.

## Exact Finite-Matrix Surface

For every positive `m`, define the complex Hilbert block

```text
H_m(i,j) = 1/(i+j+1),  i,j : Fin m.
```

The batch must prove:

```text
IsUnit (det H_m),
(H_m)^(-1)(0,0) = m^2,
```

and a finite-index matrix theorem transporting entrywise convergence `G_lambda -> G` to
`G_lambda^(-1) -> G^(-1)` when `det G != 0`. The `m^2` statement may be proved through a checked
Cauchy formula, shifted-Legendre/Gram argument, or an explicit inverse column. It may not be
inserted as a source proposition, typeclass assumption, or opaque declaration.

The final matrix target must instantiate these facts on the block matrix indexed by a finite
family of distinct critical parameters with derivative indices. Its limit must be block diagonal,
with one `H_m` block for each parameter.

## Required Lean Surface

Names may follow local conventions, but exact target checks must witness equivalents of:

```text
burnolLogScale
burnolX
tendsto_inner_burnolX
burnolAPhaseL2_chiOne
tendsto_sqrtLog_inner_chiOne_burnolX
burnolHilbertMatrix
burnolHilbertMatrix_isUnit_det
burnolHilbertMatrix_inv_zero_zero
tendsto_matrix_nonsingInv
tendsto_burnolGramMatrix
tendsto_burnolGramMatrix_inv
```

## Implementation Route

1. Prove logarithmic moment formulas on `(lambda,1]`, including an integration-by-parts bound for
   unequal critical parameters and all normalization limits as `lambda -> 0+`.
2. Expand the F2 spectral main derivative, isolate the top logarithmic term, and use the retained
   uniform small/large representative bounds to prove all scalar Gram limits.
3. Identify the second-phase image of `chi1` with the sinc-minus-Hardy representative and prove
   the target-pairing limits, including the exact `k=0` value `(s-1)/s^2`.
4. Formalize the finite Hilbert block, prove nonsingularity and the top-left inverse entry `m^2`,
   and prove continuity of nonsingular matrix inversion.
5. Package scalar limits into the finite block Gram matrix and its inverse. No projection or F4
   distance inequality is part of this batch.

## Batch Gates

- Gate A scalar moment infrastructure does not close F3.
- Gate B Gram limits without the target pairings do not close F3.
- Gate C a Hilbert inverse formula without the actual Burnol block-matrix instantiation does not
  close F3.
- No `sorry`, `admit`, project axiom, unchecked `constant`, opaque premise, or source theorem
  postulated as a variable is permitted.
- F4 and F5 remain forbidden until every exact F3 target and axiom audit passes locally and in
  public CI.

## Frontier

- `hard_gap_before`: G4/F3 open and selected; F4-F5 open; M2/G3 historically unselected (open under V4.1).
- `assumption_frontier_before`: Burnol's normalized Gram limits, target-pairing limits,
  Hilbert/Cauchy inverse entry, and finite matrix inverse limit remain external facts.
- `expected_hard_gap_delta`: close F3 only and select F4 next.
- `hard_gap_after_on_success`: F3 complete; F4 selected; F5 and M2/G3 unchanged.

## Result Rules

- `KNOWN_THEOREM_FORMALIZED`: all scalar and finite-matrix surfaces compile and pass exact target,
  axiom, local, and public CI checks.
- `DEPENDENCY_GAP_IDENTIFIED`: the source proof is narrowed to a missing theorem that is not
  inserted as a premise; F3 remains selected.
- `BRANCH_FALSIFIED`: a source normalization, target value, matrix orientation, or inverse entry
  is inconsistent after exact Lean checking.
- `NO_PROGRESS`: only generic integral or matrix wrappers compile.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; resumed from the automatic thread summary and verified
  all source-of-truth files before editing

## Local Verification Result

All preregistered scalar, target, Hilbert, and finite-matrix surfaces now compile in
`LeanLab/Riemann/BurnolGram.lean`. The final finite-family theorem permits a separate natural
number `multiplicity a` for each distinct critical parameter and uses the dependent index
`Sigma a, Fin (multiplicity a)`; its limit is the corresponding unequal-size block diagonal of
Hilbert matrices. The limiting block matrix has a checked right inverse, nonzero determinant,
explicit block inverse, and the actual finite Gram inverses converge to it.

The physical target route proves the exact `sinc - M sinc` representative, an explicit
`O(t^2)` bound at zero, large-end integrability, cutoff removal, and both normalized target
pairing cases. Exact target witnesses and the axiom audit pass, every new audited endpoint uses
only `propext`, `Classical.choice`, and `Quot.sound`, and the full local build passes with 8613
jobs. Placeholder and explicit-declaration scans and `git diff --check` are clean.

The implementation commit and public Lean Action CI were still pending at this checkpoint.
Therefore the local gates were complete, but F3 remained selected and F4-F5 remained forbidden
until the public gate passed.

## Published Result

Implementation commit `897e35b16ad3039c069d86f0c35f89d4bce526ad` passed public Lean Action
CI run `29289392653`, build job `86949324989`, in 2m7s. The batch result is
`KNOWN_THEOREM_FORMALIZED`: F3 is complete and F4 is selected but not started. F5 was unchanged;
M2/G3 is open under V4.1, and no unconditional RH claim is made.
