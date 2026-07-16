# R5 Gaussian Prime-Kernel Sign Audit Preregistration

Audit: `AUDIT-20260716-R5-GAUSSIAN-PRIME-KERNEL-SIGN-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

Mode: `DISCOVERY -> FALSIFICATION`

## Fixed Proposition

For the already compiled symmetric Gaussian von-Mangoldt weight at the actual prime `n=2`,
construct a positive Gaussian width and two real shifts for which the resulting real symmetric
`2 x 2` translation-kernel matrix is neither positive semidefinite nor negative semidefinite.
The indivisible endpoint is

```lean
def symmetricGaussianPrimeKernelMatrix
    (a : R) (b : Fin 2 -> R) (n : N) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => (symmetricGaussianVonMangoldtWeight a (b i - b j) n).re

theorem exists_pos_symmetricGaussianPrimeKernelMatrix_indefinite :
    exists a : R, exists b : Fin 2 -> R,
      0 < a and
      not (symmetricGaussianPrimeKernelMatrix a b 2).PosSemidef and
      not (-symmetricGaussianPrimeKernelMatrix a b 2).PosSemidef
```

The formal file may use Lean Unicode and an equivalent explicit `Fin 2` vector notation. It must
use the existing arithmetic weight, the actual von-Mangoldt value at `2`, and exact inequalities.
A normalized surrogate kernel or a floating-point matrix is not the endpoint.

## DAG Position And Scope

- `node_id`: W2
- `gap_id`: G7
- `hard_gap_before`: unconditional positivity of the complete Weil arithmetic form is open
- `hard_gap_after` on success: unchanged
- `hard_gap_delta`: 0
- `classification` on success: `BRANCH_ELIMINATED`
- The result rules out only a termwise local-place proof that assigns one semidefinite sign to
  each individual symmetric Gaussian prime-power translation kernel. It does not rule out
  cancellation between the pole, archimedean, and complete prime sums.
- The full fixed-width Gaussian arithmetic kernel is already Lean-equivalent to RH, so no claim of
  unconditional positivity for that full kernel is admissible here.

## Five-Candidate Screen

1. **Every individual prime-power kernel is positive semidefinite.** The `n=2`, two-shift test
   reduces to comparing the diagonal value with the value at shift difference `log 2`; the latter
   is the candidate obstruction.
2. **The negative of every individual prime-power kernel is positive semidefinite.** A positive
   diagonal entry is the immediate opposing test.
3. **The pole kernel is independently positive semidefinite.** Its translation profile is a
   positive multiple of `cosh(d/2)`, so the same two-point Gram test is adverse. This claim is not
   used as a premise and is deferred unless needed in the fixed proof.
4. **The complete fixed-width arithmetic kernel is positive semidefinite by local assembly.** The
   compiled fixed-width criterion proves that assertion is equivalent to RH; it is rejected as a
   hidden endpoint, not admitted as an auxiliary lemma.
5. **One actual prime-power Gaussian kernel is genuinely indefinite.** This survives the symbolic
   boundary tests and is selected as the exact falsification endpoint.

No rejected candidate is a downstream premise. The only admitted proposition is Candidate 5.

## Exact Witness Mechanism

Let `L = log 2`, `a = L^2 / 16`, and use shifts `0` and `L`. After extracting the common positive
factor from `symmetricGaussianVonMangoldtWeight a d 2`, the diagonal value is proportional to
`exp(-4)`, while the off-diagonal value is proportional to
`(1 + exp(-16)) / 2`. Exact exponential inequalities make the off-diagonal strictly larger.
The coefficient vector `(1,-1)` therefore gives a negative quadratic value. A coordinate vector
sees the strictly positive diagonal, so the negated matrix also fails positive semidefiniteness.

Every one of these reductions must be checked in Lean; the prose calculation is only the
preregistered proof plan.

## Closest Literature And Novelty Boundary

- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, studies positivity
  of the full Weil distribution through a compressed operator, not termwise positivity of the
  individual Gaussian prime kernels: https://arxiv.org/abs/2006.13771
- Suzuki, *Weil's quadratic form via the screw function*, treats the complete Weil form through a
  continuous-function framework and finite-interval operators: https://arxiv.org/abs/2606.09096
- The project formula in `WeilSymmetricGaussianFamily.lean` gives the exact local kernel audited
  here.

No exact published statement matching the selected two-point counterexample was located in the
targeted search. This is not a novelty determination, and no novelty claim is allowed.

## Fixed Proof DAG

1. Rewrite the complex square-root prefactor as the cast of a positive real power.
2. Prove the exact `n=2` weight formulas at differences `0` and `log 2` for
   `a=(log 2)^2/16`.
3. Prove the off-diagonal value is strictly larger than the diagonal value using exact real
   exponential inequalities.
4. Evaluate the matrix quadratic on `(1,-1)` and contradict positive semidefiniteness.
5. Prove the diagonal is positive and contradict positive semidefiniteness of the negated matrix.
6. Add exact target/type witnesses, axiom audit, repository scans, full build, and independent
   public CI evidence.

## Rejection Conditions

- Reject any proof that replaces `ArithmeticFunction.vonMangoldt 2` by an assumed positive
  constant without proving the connection.
- Reject floating-point evaluation, `native_decide`, `sorry`, `admit`, project axioms, unsafe
  declarations, or resource-limit relaxations.
- If the exact arithmetic-weight rewrite fails under two independent approaches, close as
  `NO_PROGRESS`; do not weaken the endpoint to the normalized surrogate shape.

## Local Result

The exact endpoint compiles in `LeanLab/Riemann/WeilGaussianPrimeKernelSignAudit.lean`. Lean proves
the actual complex arithmetic weight equals its real kernel, the explicit width is positive, the
two exact kernel values have factors `exp(-4)` and `(1+exp(-16))/2`, and the off-diagonal is
strictly larger. Matrix positive-semidefiniteness is then contradicted by `(1,-1)`, while positive
diagonal value contradicts positive-semidefiniteness of the negated matrix.

The standalone module, exact Targets/TargetChecks, four selected axiom prints, repository scans,
aggregate import, `git diff --check`, and full 8,679-job build pass. The axiom prints contain only
`propext`, `Classical.choice`, and `Quot.sound`. Publication and public CI remain before closure.

The immutable preregistration commit `672f965556fbd68f74e9c5e8d322e46b97db7fed` passed public
Lean Action CI run `29462185050`, build job `87507838744`, before implementation publication.

Implementation commit `01ea63517670a81b8c640de1135dec62d44436b9` passed public Lean Action CI
run `29462677629`, build job `87509304721`, in `1m54s`. Publish the immutable evidence backfill and
require its own public CI before closing the audit.

Evidence commit `af7848aea84287329ce50900d5e425538165baaa` passed public Lean Action CI run
`29462828680`, build job `87509738532`, in `1m58s`. The exact audit is publicly closed as
`BRANCH_ELIMINATED`; implementation and evidence are independently public-built.
