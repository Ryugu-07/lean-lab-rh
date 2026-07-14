# G4-F4 Burnol Finite-Zero-Set Lower Bound

Date: 2026-07-14

- `batch_id`: `BATCH-20260714-G4-F4`
- `node_id`: `B1`
- `gap_id`: `G4/F4`
- `work_class`: `SOURCE_FORMALIZATION`
- `status`: active
- `hard_gap_before`: F3 complete; F4 selected; F5 open; M2/G3 parked and unchanged.
- `assumption_frontier_before`: the finite orthogonal-projection distance inequality and the
  finite-zero-set liminf assembly are external facts.

## Source Audit

The pinned Burnol v2 TeX source was rechecked at SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.

- Lines 649-654 choose finitely many zeros and all derivative vectors below their multiplicities.
- Lines 655-663 compare `D(lambda)` with the norm of their orthogonal projection and write that
  projection using the finite inverse Gram matrix and the `chi1` pairings.
- Lines 664-670 use the F3 block Hilbert limit and inverse `(0,0)=m_rho^2`, giving the finite sum
  of `m_rho^2 / |rho|^2`.

## Interface Audit

- Mathlib defines the canonical natural multiplicity as
  `analyticOrderNatAt riemannZeta rho = (analyticOrderAt riemannZeta rho).toNat`.
- Finiteness can be proved from `analyticOn_riemannZeta` on the connected punctured plane and the
  nonzero value `riemannZeta 0 = -1/2`; positivity then follows from the zero at `rho`.
- `burnolY_mem_modelKernelSpan_orthogonal` already proves the required analytic-order
  orthogonality for each derivative vector.
- F3's `burnolFiniteGramMatrix` uses entries `inner (v j) (v i)`, while Mathlib's
  `Matrix.gram` uses `inner (v i) (v j)`. F4 must make this transpose explicit.
- Mathlib has verified orthogonal projections for finite-dimensional spans and the standard
  `le_infDist` characterization. No ready-made inverse-Gram projection formula was found.

## Selected Route

Prove a generic explicit Gram-inverse projection theorem for `Matrix.gram`, then instantiate it
on the dependent finite zero/derivative index. Use F3 to prove eventual invertibility and
convergence of the scaled target vector and inverse Gram matrix. Evaluate the limiting block
quadratic form at the `k=0` coordinates, convert the critical-line target factor to
`1 / norm(rho)^2`, and pass the resulting eventual projection lower bound through `ENNReal`
`liminf`.

## Attempt Log

### Loop 1: preregistration and interface audit

- Result: active.
- Useful finding: `analyticOrderNatAt` removes the need for an ad hoc multiplicity definition.
- Useful finding: the finite-order proof can be internal; it is not an additional RH assumption.
- Useful finding: using the conventional `Matrix.gram` isolates the only transpose issue in the
  bridge to F3 and lets Mathlib's checked Gram norm identity handle the projection energy.
- Next obstruction: compile the canonical multiplicity lemmas and the generic finite projection
  formula before instantiating the Burnol family.
- Classification: `FORMALIZATION_ONLY`; no F4 endpoint or RH progress yet.

### Loop 2: canonical multiplicity and generic finite projection

- Result: internal Lean checkpoint complete; F4 remains active.
- `analyticOrderAt_riemannZeta_ne_top_of_isNontrivialZero` transports finite analytic order from
  `rho=0` across the connected domain `{1} complement`; `riemannZeta_zero` supplies the checked
  nonvanishing base point.
- `burnolZetaZeroMultiplicity_cast` identifies the canonical natural order with the original
  `ENat` order, and `burnolZetaZeroMultiplicity_pos` proves every selected zero contributes at
  least one derivative coordinate.
- `finiteGramProjection` uses the inverse of Mathlib's conventional `Matrix.gram`. Lean verifies
  the exact row equation, membership in `span(range v)`, and orthogonality of `x-P_v x`.
- `norm_finiteGramProjection_le_infDist` constructs the finite-dimensional orthogonal projection
  instance and proves `norm(P_v x) <= infDist x K` whenever every `v i` lies in `K orthogonal`.
  No projection inequality is assumed.
- A first parser failure came from incorrect escaped Unicode code points for matrix-vector
  multiplication and orthogonal complement; replacing the former by `Matrix.mulVec` and copying
  the repository's exact orthogonal symbol resolved it without changing any statement.
- Verification: `lake env lean LeanLab/Riemann/BurnolFiniteLowerBound.lean` passes with no proof
  placeholders; only two non-fatal `unnecessarySimpa` linter suggestions remain.
- Next obstruction: instantiate the dependent zero/derivative family, bridge F3's transposed Gram
  orientation to `Matrix.gram`, and prove eventual determinant nonvanishing near `lambda=0+`.
- Classification: `FORMALIZATION_ONLY`; the finite Burnol asymptotic and liminf endpoint remain
  open.

### Loop 3: Burnol family instantiation and asymptotic pipeline

- Result: internal Lean checkpoint complete; F4 remains active.
- `burnolConventionalGramMatrix_eq_transpose` explicitly reconciles F3's stored entries
  `inner (v j) (v i)` with Mathlib's conventional `Matrix.gram` entries `inner (v i) (v j)`.
  The unequal-size Hilbert block is proved symmetric, so the conventional Gram and its inverse
  converge to the same F3 limit.
- Determinant continuity gives eventual nonsingularity of the actual conventional Gram matrix.
- For every dependent derivative index below the canonical multiplicity,
  `burnolFiniteVector_mem_modelKernelSpan_orthogonal` derives the exact `ENat` order inequality
  from `Fin.isLt` and applies F2 orthogonality. The resulting explicit finite projection satisfies
  `norm <= burnolDistance`; no geometric premise is imported.
- The scaled target vector converges coordinatewise to `(rho-1)/rho^2` at derivative zero and to
  zero otherwise. Inverse-Gram coefficients and the real Gram quadratic energy then converge.
- A product-space continuity proof for matrix-vector multiplication timed out during dependent
  `Sigma` typeclass reduction. Replacing it with checked coordinatewise finite sums reduced the
  file to a normal 3.6-second compile without increasing `maxHeartbeats`.
- Verification: `lake env lean LeanLab/Riemann/BurnolFiniteLowerBound.lean` passes without
  `sorry`; current output contains only linter/deprecation warnings.
- Next obstruction: evaluate the limiting block energy exactly, prove the critical-line norm
  identity, and identify the scaled energy with the square of the actual finite projection norm.
- Classification: `FORMALIZATION_ONLY`; the exact finite sum and liminf endpoint remain open.

### Loop 4: exact limiting energy and scaled projection identity

- Result: internal Lean checkpoint complete; F4 remains active.
- The limiting block quadratic form is evaluated exactly. Positivity of each canonical
  multiplicity selects the zeroth derivative coordinate, F3's inverse Hilbert entry contributes
  the square of that multiplicity, and the critical-line identity converts the target norm to
  `1 / norm(rho)^2`.
- `burnolScaledProjectionEnergy_eq_norm_sq` identifies the real Gram quadratic form with the
  norm square of its represented finite vector using Mathlib's checked Gram identity.
- `burnolScaledProjectionVector_eq_smul` then identifies that vector with
  `sqrt(burnolLogScale lambda)` times the actual finite zeta projection. An initially implicit
  use of `Finset.smul_sum` left scalar/module metavariables unresolved; exposing the complex
  scalar and coefficient types made the distributivity and `smul_smul` step check directly.
- Consequently `burnolScaledZetaProjectionEnergy_eq_sq` now proves the exact square identity
  needed for the norm-limit passage.
- Verification: `lake env lean LeanLab/Riemann/BurnolFiniteLowerBound.lean` passes without proof
  placeholders; output is limited to linter/deprecation warnings.
- Next obstruction: derive convergence of the nonnegative scaled projection norm from its square,
  establish its eventual pointwise comparison with the scaled distance, and pass that comparison
  through `ENNReal` `liminf`.
- Classification: `FORMALIZATION_ONLY`; the exact finite-Finset liminf endpoint remains open.

### Loop 5: projection-norm limit and finite-set liminf endpoint

- Result: exact F4 endpoint compiles; repository gates remain pending.
- Continuity of the real square root converts convergence of the checked projection energy into
  convergence of the nonnegative scaled projection norm. The proof explicitly uses
  `sqrt(x^2)=abs(x)` and nonnegativity of both the square-root scale and the Hilbert norm.
- On a common eventual right-neighborhood of zero, `lambda` is positive and at most one and the
  conventional Gram determinant is nonzero. The generic projection comparison therefore gives
  the pointwise scaled norm lower bound for `burnolDistance`.
- `ENNReal.ofReal` preserves that inequality; the convergent lower function has liminf equal to
  the finite square-root constant, so `Filter.liminf_le_liminf` proves the finite-family bound.
- Taking the index type to be the member subtype of a `Finset` of nontrivial zeros makes the zero
  map injective. RH supplies the critical-line equation, and `Finset.sum_attach` converts the
  subtype sum back to the exact public finite-set statement, including the empty set.
- Verification: the exact theorem
  `RiemannHypothesis.burnolDistance_liminf_ge_finset` passes
  `lake env lean LeanLab/Riemann/BurnolFiniteLowerBound.lean` without proof placeholders.
- Next obstruction: complete the integration, target, axiom, full-build, forbidden-token, public
  commit, and public-CI gates before declaring F4 closed or selecting F5.
- Classification: `KNOWN_THEOREM_FORMALIZED` provisionally; F4 remains active until all batch
  gates pass.

### Loop 6: repository integration and local gates

- Result: all local gates pass; public commit and CI remain.
- The new module is imported by `LeanLab.lean`. `TargetChecks.lean` contains the exact finite-set
  theorem type, and `AxiomsAudit.lean` checks the canonical multiplicity, projection comparison,
  and final endpoint transitively.
- The audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build` passes with 8614 jobs. The new source file compiles without warnings; placeholder,
  explicit `axiom`/`constant`/`opaque`, `native_decide`, heartbeat-relaxation, ignored-artifact,
  and whitespace scans are clean.
- Next obstruction: publish the implementation commit and require successful public Lean Action
  CI before closing F4, selecting F5, or starting any F5 proof work.
- Classification: `KNOWN_THEOREM_FORMALIZED` pending the public gate; M2/G3 remain unchanged.
