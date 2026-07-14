# G4-F4 Burnol Finite-Zero-Set Lower Bound Pre-Registration

Date: 2026-07-14

Batch ID: `BATCH-20260714-G4-F4`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F4`
- `work_class`: `SOURCE_FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: preregistered

Formalize Burnol's lower bound for every finite set of nontrivial zeta zeros under RH. This is
one indivisible batch: canonical zeta-zero multiplicities, finite Gram-inverse projection,
comparison with the model distance, the scaled finite quadratic-form limit, and the final liminf
statement must all compile. A generic projection lemma, an eventually-invertible Gram matrix, or
an asymptotic quadratic form alone does not close F4.

## Primary Source

Jean-Francois Burnol, *A lower bound in an approximation problem involving the zeros of the
Riemann zeta function*, arXiv `math/0103058v2`, TeX source SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.

- Source lines 649-654 select a finite nonempty set of zeros and derivative vectors.
- Source lines 655-663 bound the distance by the norm of the finite orthogonal projection and
  express that projection through the inverse Gram matrix and target pairings.
- Source lines 664-670 use the F3 Hilbert-block limit and inverse `(0,0)=m_rho^2` to obtain the
  finite sum `sum_rho m_rho^2 / |rho|^2`.

The Lean endpoint also covers the empty finite set, where the lower bound is zero.

## Exact Endpoint

Names may follow local conventions, but `TargetChecks.lean` must witness a theorem equivalent to

```lean
theorem RiemannHypothesis.burnolDistance_liminf_ge_finset
    (hRH : RiemannHypothesis)
    (R : Finset {rho : Complex // IsNontrivialZero rho}) :
    ENNReal.ofReal (Real.sqrt (
      ∑ rho in R,
        (burnolZetaZeroMultiplicity (rho : Complex) : Real) ^ 2 /
          ‖(rho : Complex)‖ ^ 2)) ≤
      Filter.liminf (fun lambda : Real =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Set.Ioi 0))
```

Here `burnolZetaZeroMultiplicity rho` must be definitionally or propositionally tied to
`analyticOrderNatAt riemannZeta rho`. It may not be an independent datum attached to the finite
set.

## Assumption Frontier

The final theorem may assume only:

- `hRH : RiemannHypothesis`;
- a finite set whose elements carry `IsNontrivialZero` proofs.

The implementation must prove in Lean:

- `analyticOrderAt riemannZeta rho != top` at every nontrivial zero;
- `0 < analyticOrderNatAt riemannZeta rho` at every nontrivial zero;
- the cast identity from the natural order back to `analyticOrderAt` needed by F2 orthogonality;
- under `re(rho)=1/2`,
  `norm ((rho-1)/rho^2)^2 = 1/norm(rho)^2`;
- every retained `burnolX lambda rho k` belongs to the orthogonal complement of the model span.

No finite-order, linear-independence, projection, distance, asymptotic, or liminf statement may be
introduced as a hypothesis. No off-critical zero branch is part of this RH-conditional batch.

## Finite Projection Surface

For a finite family `v : iota -> E`, the batch must prove the Gram-inverse coefficient formula
when `det (Matrix.gram Complex v) != 0`. Applied to the dependent index
`Sigma a, Fin (multiplicity a)`, it must show that the explicit finite sum is the orthogonal
projection of `burnolChiOneL2` onto `span Complex (Set.range v)`.

If every `v i` lies in `K orthogonal`, the proof must derive

```text
norm(projection of x onto span(v)) <= infDist x K.
```

This comparison must be checked pointwise against all members of `K` or through Mathlib's
verified orthogonal-projection API. It may not be asserted as a geometric source fact.

Because `BurnolGram.lean` stores entries as `inner (v j) (v i)`, the transpose/conjugation
orientation must be reconciled explicitly with `Matrix.gram Complex v`. A silently transposed
quadratic form fails the batch.

## Asymptotic Assembly

Put `L(lambda)=burnolLogScale lambda`, and let

```text
u_lambda(rho,k) = sqrt(L(lambda)) * inner (X(lambda,rho,k)) chi1.
```

The batch must combine F3 to prove:

- the conventional Gram matrix and its inverse converge to the unequal-size block Hilbert
  matrix and its inverse;
- `u_lambda(rho,k)` converges to `(rho-1)/rho^2` for `k=0` and to zero otherwise;
- the corresponding real quadratic form converges to
  `sum_rho multiplicity(rho)^2 / norm(rho)^2`;
- eventually the quadratic form is the square of the scaled finite projection norm;
- the scaled projection norm converges to the square root of that finite sum.

The final lower bound must then pass the eventual pointwise projection inequality through
`Filter.liminf` in `ENNReal`. All `ofReal`, square-root, nonnegativity, and multiplication
conversions must be proved.

## Implementation Route

1. Define the canonical zeta-zero multiplicity and prove finite, positive, and cast-back lemmas.
2. Prove a reusable finite Gram-inverse projection theorem with audited matrix orientation and a
   distance lower bound against an orthogonal submodule.
3. Instantiate the theorem on the finite zero family and obtain eventual Gram invertibility from
   the F3 nonsingular Hilbert-block limit.
4. Prove convergence of the scaled target vector, inverse-Gram coefficients, projection energy,
   and projection norm; evaluate the limiting block quadratic form exactly.
5. Combine the eventual distance inequality with the convergent finite projection norm and close
   the exact `ENNReal` liminf endpoint.

## Batch Gates

- Gate A canonical multiplicity lemmas do not close F4.
- Gate B generic finite-dimensional projection infrastructure does not close F4.
- Gate C the finite quadratic-form limit without the model-distance inequality does not close F4.
- Gate D an eventual distance inequality without the exact finite sum and liminf endpoint does
  not close F4.
- No `sorry`, `admit`, project `axiom`, unchecked `constant`, `opaque` premise, or source theorem
  postulated as a variable is permitted.
- F5 remains forbidden until the exact F4 endpoint, target checks, axiom audit, full local build,
  public commit, and public CI all pass.

## Frontier

- `hard_gap_before`: F3 complete; F4 open and selected; F5 open; M2/G3 parked and unchanged.
- `assumption_frontier_before`: Burnol's finite orthogonal-projection distance inequality and
  finite-zero-set liminf assembly remain external source mathematics.
- `expected_hard_gap_delta`: close F4 only and select F5 next.
- `hard_gap_after_on_success`: F4 complete; F5 selected; M2/G3 unchanged.

## Result Rules

- `KNOWN_THEOREM_FORMALIZED`: the exact finite-Finset liminf endpoint compiles and passes exact
  target, axiom, local, and public CI checks.
- `DEPENDENCY_GAP_IDENTIFIED`: the source proof is narrowed to a missing theorem that is not
  inserted as a premise; F4 remains selected.
- `BRANCH_FALSIFIED`: the source normalization, matrix orientation, projection formula, or finite
  constant is inconsistent after exact Lean checking.
- `NO_PROGRESS`: only generic finite-dimensional or filter wrappers compile.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; resumed from the automatic thread summary and verified
  the repository, source audit, and relevant Mathlib interfaces before preregistration

## Local Verification Result

All preregistered F4 surfaces now compile in
`LeanLab/Riemann/BurnolFiniteLowerBound.lean`. The canonical multiplicity is
`analyticOrderNatAt riemannZeta`; Lean proves its finite analytic order and positivity at every
nontrivial zero. A generic inverse-Gram finite projection is proved to lie in the finite span,
have the required residual orthogonality, and have norm at most the model distance when its
vectors lie in the model-space orthogonal complement.

For the actual dependent Burnol family, Lean checks the transpose orientation, eventual Gram
invertibility, scaled target and inverse-coefficient limits, exact limiting energy
`sum m_rho^2 / norm(rho)^2`, the scaled projection-norm limit, and the eventual distance
comparison. `ENNReal` liminf monotonicity then gives the exact finite-Finset endpoint, including
the empty set.

The exact target witness and transitive axiom audit pass; the audited endpoints depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The full local build passes with 8614 jobs, and
placeholder, explicit-declaration, resource-relaxation, ignored-artifact, and whitespace scans
are clean. The implementation commit and public Lean Action CI are pending, so F4 remains selected
and F5 remains forbidden at this checkpoint.
