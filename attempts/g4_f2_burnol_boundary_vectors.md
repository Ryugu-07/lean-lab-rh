# G4-F2 Burnol Boundary Vectors

Date: 2026-07-13

- `batch_id`: `BATCH-20260713-G4-F2`
- `node_id`: `B1`
- `gap_id`: `G4/F2`
- `work_class`: `SOURCE_FORMALIZATION`
- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `hard_gap_before`: F2 selected; F3-F5 open; M2/G3 historically unselected (open under V4.1).
- `hard_gap_after`: F2 complete; F3 selected; F4-F5 and M2/G3 unchanged.
- `hard_gap_delta`: closed exactly the fixed Burnol boundary-vector edge.

## Successful Route

1. Construct the total critical-line phase from `burnolZ`, totalizing zeros by `1`, and package
   multiplication by the phase and its conjugate as inverse complex `L2` isometries. Construct
   physical time reversal, normalized dilation, cutoff, and `burnolPsiL2`.
2. Define Burnol's oscillatory continuation `burnolPhi` directly. Prove its integral and series
   formulas, all-order parameter derivatives, small-end Gamma main plus uniform series remainder,
   and large-end estimates after two Hardy averages.
3. Prove the exact Mellin transforms of `phi`, `(1-M)^2 phi`, and `psi`, including every Fubini and
   Bochner-integrability obligation. Fourier-Mellin injectivity then gives the exact interior phase
   identity and identifies `burnolPreY` with the physical cutoff of the Hardy-square vector.
4. Package the explicit cutoff representative in `L2`. Local parameter bounds produce one square-
   integrable majorant; filter dominated convergence yields the critical-line `L2` limit
   `tendsto_burnolPreY`, from which `burnolY` is obtained through the inverse phase.
5. Retain the explicit representative: zero below `lambda`, a lambda-independent bounded
   spectral-main error on `[lambda,1]`, and an explicit `(1+abs(log t))^2/t` bound above `1`.
6. Pass the pre-boundary Mellin pairing through the `L2` limit. Conjugation symmetry converts the
   reflected source to Burnol's direct `(-1)^k` derivative formula. The zeta functional equation
   factors the reflected source by `riemannZeta`; analytic order annihilates all Leibniz terms.
   Span induction then proves orthogonality to `burnolModelKernelSpan lambda`.

## Rejected Or Corrected Routes

- The F1b distance isometry `T` was not reused as the second phase `V`; the source multipliers are
  different.
- Gate A infrastructure and left-half-plane pairings were kept local until the oscillatory
  continuation, boundary limit, physical estimates, and full-span orthogonality also compiled.
- `Y` was not defined by selecting an element of an orthogonal complement, and derivative
  vanishing was not assumed. Both are consequences of explicit source formulas.
- The initial boundary pairing was naturally obtained with the model kernel in Lean's first inner
  argument. A separate checked conjugation/reflection chain was added to expose Burnol's direct
  source formula rather than leaving the equivalence in prose.

## Lean Surface And Verification

- Module: `LeanLab/Riemann/BurnolY.lean`.
- Central names: `burnolAPhaseL2`, `burnolTimeReverseL2`, `burnolCutoffL2`, `burnolPsiL2`,
  `burnolPreY`, `burnolPhi`, `burnolYTransformed`, `burnolY`, `tendsto_burnolPreY`,
  `inner_burnolY_normalizedModelKernel`, and
  `burnolY_mem_modelKernelSpan_orthogonal`.
- Exact boundary-limit, representative-bound, pairing, and orthogonality witnesses compile in
  `TargetChecks.lean`.
- Full `lake build` passes with 8612 jobs. Incomplete-proof and explicit-declaration scans are
  empty; `git diff --check` passes.
- All audited F2 surfaces depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed).
- `reasoning_effort`: not exposed.
- `budget`: unbounded persistent-goal budget.
- `compaction_state`: automatic compaction occurred during implementation; work resumed from the
  retained fixed-batch checkpoint and the source frontier was rechecked before closure.
- `implementation_SHA`: `21f600b6de9e859dc9d912a82db6411547bae325`.
- `public_CI`: success, run `29278978470`, build job `86915163555`.

This closes known source mathematics for F2. It does not prove RH, reduce M2/G3, establish the F3
Gram asymptotics, or prove the F4/F5 lower-bound statements.
