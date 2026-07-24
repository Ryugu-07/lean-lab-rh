# H7 Weil Volterra Source Calculus Preregistration

Date: 2026-07-24

Campaign: `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-01`

Selected node: `H7-WEIL-VOLTERRA-SOURCE-CALCULUS-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_PENDING`

## Baseline

- `parent_commit`: `c4287392fe4ba0e9d588aca1b13121ae13a27654`.
- `parent_public_ci`: Lean Action run `29983416809`, build job `89129994376`, passed in `1m34s`.
- `route_selection`: `research/route_selection_post_h1_j_contour_20260724.md`.
- `global_goal`: active; RH remains open.
- `production_gate`: no production Lean source may be created before this preregistration commit
  passes public Lean Action CI.

## Primary source alignment

The fixed source is Groskin, arXiv:2607.02828, Lemma 2.3 and the prime leg of Theorem 2.5.
For a centered finite coefficient vector `u`, define

```text
T_u(t) = sum_m u_m exp(2*pi*i*m*t),
K_u(omega) = 2 * integral_0^omega T_u(t) T_u(omega-t) dt.
```

For

```text
psi_(alpha,omega)(x) = alpha/pi * sin(2*pi*omega*x),
```

the divided-difference matrix uses the source derivative on its diagonal and the value quotient
off the diagonal. The source identity is `u^T Q u = alpha*K_u(omega)` for real symmetric `u`.

For integer cutoff `C>=2`, the actual prime atom has

```text
alpha_q = -Lambda(q)/sqrt(q),
omega_q = 1-log(q)/log(C).
```

The induced Fourier weight has band `Delta=log(C)/(2*pi)` and maps
`xi_q=log(q)/(2*pi)` to `omega_q`.

## Fixed Lean endpoint

Create `LeanLab/Riemann/WeilFiniteDictionarySourceCalculus.lean` and prove all of the following
from literal source objects.

1. Define the centered complex trigonometric polynomial `T_u` and the actual interval-integral
   Volterra kernel `K_u`. Prove that reflection-even real coefficients make `T_u` and `K_u`
   real-valued on real arguments.
2. Define the generic sine source, its exact derivative samples, and its finite
   divided-difference matrix. Prove the entry formula separately on and off the diagonal.
3. Evaluate the pairwise Volterra exponential integral, retaining the `m=n` branch. Sum the
   identity to prove

```text
u dot (Q_(alpha,omega) * u) = alpha * re(K_u(omega)).
```

   For reflection-even `u`, package the source's real-valued equality.
4. Prove finite atomic superposition: the quadratic form of a finite sum of sine-source matrices
   is the corresponding finite sum of Volterra values.
5. Identify the existing literal `weilFinitePrimeAtomMatrix C q N` with the generic sine-source
   matrix at `alpha_q,omega_q`, and deduce the exact actual-prime identity

```text
u dot (weilFinitePrimeSourceMatrix C N * u)
  = sum_(2<=q<=C) alpha_q * re(K_u(omega_q)).
```

6. Define the source band-limited Fourier weight `hat(g_u)`. Prove evenness, vanishing outside
   `[-Delta,Delta]`, and for `2<=q<=C` the exact coordinate identity

```text
hat(g_u)(log(q)/(2*pi)) = pi * re(K_u(1-log(q)/log(C))).
```

7. Rewrite the actual prime quadratic as the literal finite prime side of the induced
   explicit-formula test.

The final theorem must package items 1--7 and be registered as one proven Target only after all
mechanical gates pass.

## Decision criteria

- `FULL_SUCCESS_AT_SOURCE_CALCULUS_ENDPOINT`: all seven items compile, including the diagonal
  branch, actual-prime instantiation, Fourier cutoff coordinate, TargetChecks, axiom audit, full
  build, and public evidence gates.
- `PARTIAL_ATOM_ONLY`: the generic atom identity compiles but the actual prime or Fourier
  coordinate does not. Record the exact mismatch; do not register the aggregate endpoint.
- `SOURCE_MISMATCH`: a factor `2`, `pi`, sign, centered-frequency orientation, diagonal
  derivative, or `omega=1-log(q)/log(C)` differs from the source. Stop and register the mismatch.
- `PREMISE_CREEP`: the proof needs an assumed integral evaluation, symmetry cancellation, or
  cutoff identity instead of deriving it for the literal finite objects. Stop without a proven
  Target.

## Known obstacles

- The interval exponential integral has a genuine diagonal branch `m=n`; replacing it with the
  off-diagonal quotient would silently lose the derivative sample.
- `K_u` is complex before reflection-even symmetry is used. The matrix equality first targets
  its real part.
- Reindexing by `Fin.rev` must use the exact centered-frequency negation theorem.
- The cutoff coordinate uses `abs(xi)` and requires `2<=q<=C` plus positivity of `log(C)`.
- The existing prime atom already carries the negative von Mangoldt coefficient; no extra minus
  sign may be inserted.

## Claim boundary

This campaign does not prove the full finite Guinand--Weil zero-sum dictionary, admissibility or
horizontal-strip decay of `g_u`, the pole transport, the archimedean transport or cutoff-free
limit, an inverse from test functions to finite vectors, density in the complete Weil class,
positivity of the total matrix, simple-even ground states, source convergence, H7, or RH.

## Mechanical gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct warning-as-error compilation, exact TargetChecks, selected transitive
`#print axioms`, an empty forbidden scan, `git diff --check`, full `lake build`, frozen
implementation CI, immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

## Production gate

Preregistration commit `b98925631116a204240b210a4f181438413700c2` passed public Lean Action
run `30070385819`, build job `89409815046`, in `1m41s`. Production proof-source editing is now
open.

## Local implementation checkpoint

The 729-line source module compiles all seven fixed items with no admitted premise. Reflection
symmetry makes the literal trigonometric polynomial real by finite `Fin.rev` reindexing and makes
the Volterra kernel real by commuting `Complex.imCLM` with the actual interval integral. Both
pair-integral branches, the generic and finite-superposition quadratics, actual prime
instantiation, Fourier support and prime coordinate, and the aggregate certificate compile.

`Targets`, the exact aggregate `TargetChecks` witness, and selected transitive axiom prints also
compile. The source-to-Lean audit is
`research/h7_weil_volterra_source_calculus_definition_alignment_20260724.md`. The forbidden scan
is empty, `git diff --check` passes, and the full `8758/8758` build succeeds. Frozen
implementation publication is next.

## Frozen implementation evidence

Frozen implementation commit `e5f011dbbf9f7c40a802ab88f9a91aa6aea3f370` passed public Lean
Action run `30072543069`, build job `89416248542`, in `2m6s`. The proof source, Target,
TargetCheck, and axiom audit are frozen. Docs-only immutable-evidence commit
`59adecc50ac343912eca3ef1989a5b4a642103e7` passed run `30072806474`, build job
`89417024378`, in `1m36s`. Only final-ledger CI remains.
