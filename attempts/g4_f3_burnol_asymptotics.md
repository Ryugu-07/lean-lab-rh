# G4-F3 Burnol Finite-Dimensional Asymptotics

Date: 2026-07-14

- `batch_id`: `BATCH-20260714-G4-F3`
- `node_id`: `B1`
- `gap_id`: `G4/F3`
- `work_class`: `SOURCE_FORMALIZATION`
- `status`: complete
- `hard_gap_before`: F3 selected; F4-F5 open; M2/G3 parked and unchanged.
- `assumption_frontier_before`: normalized Gram limits, target-pairing limits, the finite
  Hilbert/Cauchy inverse entry, and matrix inverse convergence are external facts.

## Source Audit

The pinned Burnol v2 TeX source was rechecked at SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.

- Lines 579-623 define `X(lambda,s,k)=log(1/lambda)^(-1/2-k)Y(lambda,s,k)` and give the same-zero
  Hilbert moments and distinct-zero cancellation.
- Lines 625-645 give the separately normalized `chi1` pairing, with only `k=0` surviving.
- Lines 655-670 require the inverse of the finite limiting Gram matrix and the top-left Hilbert
  inverse entry `m^2`.

## Initial Interface Audit

- F2 already exposes the exact derivative expansion of the main representative and
  lambda-independent bounds on `(lambda,1]` and `[1,infinity)`.
- F2 does not yet identify the second phase applied to `burnolChiOneL2`. The source representative
  is `sinc - HardyAverage(sinc)` and must be proved in this batch.
- Mathlib has finite Gram matrices, positive definiteness, matrix adjugates/inverses, and shifted
  Legendre polynomials. No Hilbert/Cauchy inverse theorem or top-left inverse formula was found.
- Partial scalar asymptotics or generic matrix lemmas remain internal to the indivisible F3 batch.

## Selected Route

The batch will first close the scalar logarithmic-moment API and the `chi1` phase image, then use
the explicit F2 representatives for Gram and target limits. The finite matrix layer will be proved
after the scalar limits, using a checked Hilbert-block argument and an explicit continuity proof
for nonsingular inversion.

## Lean Checkpoint 1: Scalar Gram Kernel

`LeanLab/Riemann/BurnolGram.lean` now compiles the following internal F3 layers without `sorry`:

- the logarithmic scale and normalized Burnol vector;
- exact nonoscillatory logarithmic moments on `Ioc lambda 1`;
- a recursive primitive and an explicit `O((1+log(1/lambda))^n)` bound for every nonzero
  pure-imaginary oscillatory moment;
- normalized same-critical-point limit `1/(k+l+1)` and distinct-critical-point limit `0`;
- continuous extension of `norm (burnolVSpectral s)=1` to every point on the critical line,
  including zeta zeros;
- vanishing of every lower Leibniz term with derivative-index surplus `i+j>0`;
- the complete finite double expansion and its exact identification with the truncated
  `burnolPhiHardyGammaMain` derivative pairing;
- entrywise-to-matrix convergence and continuity of nonsingular matrix inversion.

This is an internal checkpoint only. The later checkpoint below transports the pairing to the
actual `burnolYTransformed` vectors and completes the same-point Hilbert block. The `chi1` target
pairing and actual finite multi-point Burnol block instantiation remain open. F3 remains selected
and indivisible; F4-F5 remain forbidden, and M2/G3 are unchanged.

## Lean Checkpoint 2: Actual Gram Pairing and Hilbert Block

`LeanLab/Riemann/BurnolGram.lean` now additionally compiles the following internal F3 layers
without `sorry`:

- transport of the scalar asymptotics across the F2 bounded remainder and large tail, yielding
  the actual normalized `burnolYTransformed` pairing and the scalar Burnol Gram limit;
- entrywise convergence of the actual same-critical-point Gram matrix;
- an explicit Cauchy/Lagrange construction of the inverse of the finite Hilbert matrix
  `1/(i+j+1)`, including a Lean proof that its determinant is nonzero;
- exact finite-product evaluations proving that the inverse `(0,0)` entry is `(m:ℂ)^2` for an
  `m`-dimensional block;
- continuity of inversion at the actual Gram limit and convergence of the actual inverse
  `(0,0)` entry.

The Cauchy proof uses row nodes `i`, pole nodes `-(j+1)`, a nodal polynomial on the pole set, and
Lagrange interpolation on the row set. The resulting candidate is checked by matrix
multiplication before it is identified with `Matrix.inv`; the factorial product calculations then
specialize its top-left entry. This remains `FORMALIZATION_ONLY` inside the indivisible batch.
The exact second-phase image of `burnolChiOneL2`, both target-pairing cases, and the actual
multi-point finite Burnol block are still open, so F3 is not closed.

## Lean Checkpoint 3: Physical Target And Variable Multiplicity Blocks

The remaining source surfaces now compile without `sorry` or any new premise:

- `burnolAPhaseL2_chiOne` identifies the actual second-phase image with
  `burnolSinc - burnolHardyAverage burnolSinc` through Mellin/Fourier-Plancherel, not by defining
  the target as an operator image;
- `Real.sin_bound` gives an explicit quadratic sinc remainder, Hardy averaging preserves it, and
  `burnolChiOnePhase_isBigO_sq` proves the source-required `O(t^2)` decay at zero;
- physical cutoff integrals converge to the full target pairing for every derivative index, with
  the exact `k=0` value `(s-1)/s^2`; after Burnol normalization all `k>0` limits vanish;
- `burnolBlockGramMatrix` first checked the homogeneous finite-family mechanism, after which a
  source-shape audit rejected it as the final interface because zero multiplicities can differ;
- `burnolFiniteGramMatrix` uses the dependent index `Sigma a, Fin (multiplicity a)` and converges
  to the unequal-size `Matrix.blockDiagonal'` Hilbert limit for every injective finite critical
  family; a checked block right inverse proves determinant nonvanishing, the exact block inverse,
  and convergence of the actual finite Gram inverses.

The small-end proof initially failed only at real/complex coercion and set-integral scalar
normalization obligations; these were resolved with explicit `Complex.ofReal` identities,
`measureReal_restrict_apply_univ`, and `Complex.real_smul`. No weakened estimate or assumed Taylor
expansion was introduced.

## Local Verification

- `lake env lean LeanLab/Riemann/BurnolGram.lean`: pass.
- exact `TargetChecks.lean`: pass, including scalar, target, same-size block, and variable-size
  block statements.
- `AxiomsAudit.lean`: every new endpoint depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- full `lake build`: pass, 8613 jobs.
- no `sorry`, `admit`, `sorryAx`, project `axiom`, `constant`, or `opaque` declaration; `git diff
  --check` passes.

Local result: every preregistered mathematical gate is satisfied. F3 remained selected until the
implementation commit passed public CI; F4-F5 remained forbidden and M2/G3 remained parked.

## Published Verification And Result

- implementation commit: `897e35b16ad3039c069d86f0c35f89d4bce526ad`;
- public Lean Action CI: run `29289392653`, build job `86949324989`, success in 2m7s;
- classification: `KNOWN_THEOREM_FORMALIZED`;
- `hard_gap_after`: F3 complete; F4 selected but not started; F5 and M2/G3 unchanged;
- no unconditional approximation, closure membership, or proof of RH is claimed.
