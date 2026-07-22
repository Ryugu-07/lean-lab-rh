# H7 Finite Weil Matrix and Parity Preregistration

Date: 2026-07-22

Campaign: `LITERATURE-20260722-H7-WEIL-FINITE-MATRIX-PARITY-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Baseline and route decision

- `parent_commit`: `9ab3bf45101226f731b371a11ec06b149fa11a9a`.
- `baseline_public_ci`: Lean Action run `29925232284`, build job `88940549581`, passed in
  `1m55s`.
- `previous_campaign`: `LITERATURE-20260722-H7-WEIL-GROUNDSTATE-ALIGN-01` compiled the weighted
  coordinate bridge and exposed the source/project regularity gap. It did not construct the
  finite matrix or prove the source's simple-even hypothesis.
- `selected_node`: `H7-WEIL-GROUNDSTATE-FINITE-MATRIX-01`.
- `material_difference`: this campaign formalizes the source matrix's exact finite spectral
  assumption and a non-tautological certificate for it. It does not add another transform
  coordinate lemma and does not infer spectral facts from the completed M0 bridge.
- `historical_priority`: the 2025 source explicitly lists simple-even ground-state structure as
  one of two missing steps. Testing that exact step is an omission-seeking audit of the selected
  historical route, while conjecture proposal and falsification remain open under the standing
  gates.
- `global_goal`: active; no finite-dimensional result alone proves RH.

## Exact source object

For `I_N = {-N,...,N}`, let `r(i)=-i` and let `a_i,b_i` be real samples satisfying
`a_{r(i)}=a_i` and `b_{r(i)}=-b_i`. The Connes--Consani--Moscovici matrix has

```text
T(i,i) = a_i,
T(i,j) = (b_i-b_j)/(i-j)  for i != j.
```

The Groskin divided-difference matrix is the specialization `a_i=psi'(i)`, `b_i=psi(i)`.
Connes--Consani--Moscovici prove that this matrix is real symmetric, commutes with reflection,
and satisfies a rank-two commutator identity. They then define `even-simple` to mean that the
smallest eigenvalue is simple and its eigenvector is reflection-even. That property is assumed,
not proved, in the downstream spectral construction.

Represent `I_N` in Lean by `Fin (2*N+1)`, with reflection `Fin.rev` and centered coordinate
`kappa(i)=i-N`. The representation must prove `kappa(rev i)=-kappa(i)` rather than use it by
informal indexing convention.

## Preregistration evidence audit

- The source Arb file `arb_ldlt_certify.py` rigorously certifies the full `401 x 401` cutoff-free
  matrix at `c=100`, `N=200` as positive definite. Its certificate establishes inertia only; it
  does not compare the lowest even and odd eigenvalues or prove simplicity.
- The negative eigenvalues in the earlier finite-height `c=100` data are identified by the source
  `ERRATA.md` as archimedean-cutoff artifacts and disappear under a larger cutoff and the
  cutoff-free evaluation. They are not counterexamples.
- The published `c=13`, `N=4` eigenflow and finite dictionary data are even-sector calculations.
  They do not establish that the full matrix ground state belongs to that sector.
- Therefore this campaign is not preregistered as `FALSIFICATION`. A later exact witness of odd
  minimality, degeneracy, or parity crossing will receive a separate theorem-producing
  `FALSIFICATION` campaign.

## Exact mathematical target

For a real symmetric matrix `A` commuting with reflection, define

```text
R(x)(i) = x(r(i)),
e(x) = (x+R(x))/2,
o(x) = (x-R(x))/2,
q_A(x) = x dot (A*x).
```

Prove the following finite certificate theorem. Suppose `xi` and `mu` satisfy:

1. `R(xi)=xi`, `xi dot xi=1`, and `A*xi=mu*xi`;
2. every nonzero even `y` with `xi dot y=0` satisfies
   `mu*(y dot y) < q_A(y)`;
3. every nonzero odd `y` satisfies `mu*(y dot y) < q_A(y)`.

Then every vector `x` satisfies `mu*(x dot x) <= q_A(x)`, equality holds exactly for scalar
multiples of `xi`, and the `mu` eigenspace is exactly the line spanned by `xi`. Thus `mu` is a
simple ground-state eigenvalue with an even eigenvector in the source sense.

Apply the structural half of this theorem to the exact divided-difference matrix: prove symmetry,
centrosymmetry, reflection commutation, even/odd invariance, orthogonality of the parity parts,
vanishing of the mixed quadratic term, and exact quadratic splitting.

## Proposed Lean spine

The intended production module is `LeanLab/Riemann/WeilGroundStateFiniteMatrix.lean`. Final
statements may change only to match checked Mathlib APIs without weakening their mathematical
content. The proposed declarations are:

1. `weilFiniteCenteredFrequency` and its reflection-negation theorem;
2. `weilFiniteReflect`, `WeilFiniteIsEven`, and `WeilFiniteIsOdd`;
3. `weilFiniteDividedDifferenceMatrix` with separate diagonal samples `a` and off-diagonal
   samples `b`;
4. symmetry and centrosymmetry of that matrix under even `a` and odd `b`;
5. commutation of `mulVec` with reflection;
6. `weilFiniteEvenPart` and `weilFiniteOddPart`, with reconstruction, parity, orthogonality, and
   preservation by the matrix;
7. mixed-term vanishing and quadratic splitting for every symmetric reflection-commuting matrix;
8. a source-aligned predicate `WeilFiniteEvenSimpleGroundState`;
9. a predicate `WeilFiniteParityRayleighCertificate` containing the three strict conditions
   above;
10. endpoint theorem that the certificate implies `WeilFiniteEvenSimpleGroundState`, followed by
    a corollary for `weilFiniteDividedDifferenceMatrix`.

Every completed declaration receives exact TargetChecks and selected `#print axioms` entries. No
`sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource relaxation is
permitted.

## Numerical navigation probe

After the matrix and parity target are fixed, source formulas may be evaluated on a bounded grid
of `(c,N)` to compare the lowest even and odd eigenvalues and to search for multiplicity or parity
crossing. Such values are navigation evidence only. A candidate failure must be replaced by a
kernel-checked exact or interval certificate before it changes the theorem ledger. Finite success
does not imply a gap uniform in `N` or the prime cutoff.

## Success, falsification, and stopping criteria

- `success`: the exact source matrix and parity algebra compile; the strict two-block Rayleigh
  certificate compiles and implies the source-faithful simple-even predicate; all mechanical
  gates and public CI pass.
- `meaningful_partial`: the source matrix/parity algebra compiles but the certificate theorem is
  reduced to one precisely named finite-dimensional algebra or Mathlib interface obstruction.
- `falsification`: a kernel-checked source matrix instance has a lowest odd mode, a degenerate
  lowest eigenvalue, or violates a preregistered parity identity. Record a new `OBS-H7` node and
  do not continue to an infinite uniform-gap proof under the false premise.
- `no_progress`: the exact source property cannot be expressed without importing an unproved
  spectral premise. Record the boundary and route-select.
- `local_stop`: stop after the finite checker and source matrix interface are publicly closed, or
  after an exact obstruction is recorded. The uniform `(c,N)` spectral theorem and the actual
  ground-state-to-`k_lambda` limit remain separate open campaigns.

## Assumption frontier

- `before`: source papers provide the divided-difference formula and reflection symmetry, but the
  project has no exact finite matrix or checker for the assumed simple-even ground state.
- `after_on_success`: finite spectral certificates can target the correct property without
  confusing positive definiteness, even-sector positivity, or a finite eigenvalue table with
  simple-even uniformity.
- `forbidden_inference`: positive definiteness does not imply simplicity or even minimality;
  even-sector computation does not compare the odd sector; fixed finite certificates do not imply
  uniformity or RH.
- `hard_gap_before`: simple-even structure stable under Galerkin refinement and increasing prime
  cutoff is open; the true ground-state-to-`k_lambda` comparison is open.
- `hard_gap_after_if_success`: both global gaps remain open. The campaign supplies a checked
  finite decision interface and therefore has no automatic RH-frontier delta.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: one inherited compaction before preregistration; canonical governance and
  all current frontier files were reread.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit only this preregistration and its synchronized ledgers first. It must pass public Lean
Action CI before `WeilGroundStateFiniteMatrix.lean`, Targets, TargetChecks, or AxiomsAudit are
edited.
