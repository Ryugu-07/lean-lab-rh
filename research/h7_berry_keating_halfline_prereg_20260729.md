# H7 Berry--Keating Naive Half-Line Preregistration

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H7-BERRY-KEATING-HALFLINE-01`

Node: `H7-BERRY-KEATING-NAIVE-HALFLINE-01`

Mode: `LITERATURE / OMISSION_AUDIT / FALSIFICATION`

Status: `IMPLEMENTED_LOCAL / PUBLIC_IMPLEMENTATION_REQUIRED`

Preregistration commit `5ec1e2b9b5e8028517934b986f407f2a210748e6` passed public Lean
Action run `30407563102`, build job `90436305353`, in `1m40s`. Proof-source editing began only
after this gate passed.

## Primary sources and exact inference

The fixed source for the operator and half-line obstruction is Endres--Steiner:

<https://arxiv.org/abs/0912.3183>

For

```text
H_BK = -i (x d/dx + 1/2)
```

on `L^2(R_{>}, dx)`, the source solves the formal eigenvalue equation by

```text
psi_E(x) = c * x^(-1/2 + i E)
```

after setting `hbar=1`, and proves that the self-adjoint half-line realization has purely
continuous spectrum. It also proves a separate no-go theorem for fixed compact quantum graphs
from their Weyl asymptotics.

The route relation to Connes' scaling action is locked from Connes--Consani:

<https://arxiv.org/abs/1910.14368>

That paper identifies the symmetrized `PQ` operator with the generator of unitary scaling and
explains why the uncut scaling system has no discrete spectrum. It also warns that the
Berry--Keating emission picture and Connes' absorption picture have matching semiclassical
counts but are not equivalent quantum models.

No source claim about pure continuity or compact-graph Weyl asymptotics will be imported as a
Lean premise. This campaign checks only the exact formal mode and its failure to lie in the
half-line `L^2` space.

## Historical-selection reason

The project's H7 work is deep but concentrated on the 2025--2026 finite-prime Weil
ground-state program. The 1999 Berry--Keating route, its standard half-line quantization, and
the later half-line/compact-graph no-go theorems have no independent route card or compiled
endpoint. Counting all of that as already covered by the generic H7 label would hide a real
historical gap.

This node is selected ahead of another H7 finite-matrix optimization because it maps a distinct
spectral mechanism. It asks where the original `H=xp` route first needs genuinely global
arithmetic confinement. H1 global moments, H2 inverse Mellin, H10 number-field trace, H11 sparse
amplification, H13 transfer, direct RH attacks, and original conjectures remain open.

## Fixed Lean endpoint

Create `LeanLab/Riemann/BerryKeatingHalfLine.lean` without placeholders or resource relaxation.
Names may change to match local APIs, but the statements may not be weakened silently.

1. Define the unit-normalized formal mode
   `berryKeatingMode E x = (x : Complex) ^ ((-1/2 : Real) + Complex.I * E)`.
2. Define the pointwise formal differential expression
   `berryKeatingFormal f x = -Complex.I * ((x : Complex) * deriv f x + f x / 2)`.
3. Prove the exact derivative identity for every `x>0`.
4. Prove the formal eigenvalue identity
   `berryKeatingFormal (berryKeatingMode E) x = E * berryKeatingMode E x`
   for every `x>0`.
5. Prove the exact norm-square law
   `norm (berryKeatingMode E x) ^ 2 = x^-1` for every `x>0`.
6. Prove
   `not MemLp (berryKeatingMode E) 2 (volume.restrict (Set.Ioi 0))`.
7. Combine the formal eigenvalue and non-`L^2` statements in one route-audit endpoint.

The `MemLp` statement must use the restricted Lebesgue measure on `(0,+infinity)`. Replacing it
with pointwise boundedness, local integrability, or nonintegrability of the mode in `L^1` is not
success.

## Success and falsification criteria

`FULL_SUCCESS` requires all seven fixed items, exact Targets and TargetChecks, selected
standard-only axiom prints, empty forbidden scans, warning-as-error module compiles,
`git diff --check`, a full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the exact formal eigenvalue identity and an exact proof that the
same mode is not in the restricted half-line `L^2` space. Failure to package the aggregate
endpoint or an API-only registration issue may remain.

`COUNTEREXAMPLE` requires a no-sorry proof that the displayed nonzero mode belongs to the exact
restricted `L^2` space for some real `E`. A locally square-integrable or truncated mode is not a
counterexample.

## Claim boundary

- The campaign does not prove that every distributional solution of the eigenvalue ODE is a
  scalar multiple of the displayed mode.
- It does not formalize an unbounded operator domain, symmetry, essential self-adjointness,
  deficiency indices, the spectral theorem, or pure continuity.
- It does not formalize compact quantum graphs or the compact-graph Weyl no-go theorem.
- It does not rule out energy-dependent boundaries, noncompact arithmetic quotients,
  regularized traces, Connes' absorption spectrum, or other Berry--Keating modifications.
- It does not construct a Hilbert--Polya operator, locate a zeta zero, prove H7, or prove RH.

The legitimate conclusion is narrower: the standard formal half-line eigenmode is a generalized
eigenfunction, not an `L^2` eigenvector. Any successful repair must add a confinement or
absorption mechanism not present in the naive half-line model.

## Omission-sensitive successor

After this local node closes, the H7 omission question becomes:

```text
Which global arithmetic boundary or quotient can turn the scaling generalized modes into a
discrete multiplicity-bearing object while retaining the Riemann-von Mangoldt T log T count?
```

The source-backed candidates to compare are Connes' semilocal/adele-class trace formula,
Berry--Keating energy-dependent phase-space cutoffs, and noncompact graph or boundary
constructions. A fixed compact graph is not to be proposed without confronting the cited Weyl
no-go theorem.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1; no serving token budget is exposed.
- `compaction_state`: resumed from a generated summary after the H8 closure; current governance,
  census, Targets, attempts, hard-gap DAG, protected-file state, and H8 public closure
  coordinates were rechecked before selection.
- `global_goal`: active.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit and push this docs-only preregistration first. Public Lean Action CI must pass before
editing any `LeanLab/` proof source, target registry, exact check, or axiom-audit file.

This gate passed at commit `5ec1e2b9b5e8028517934b986f407f2a210748e6`, Lean Action run
`30407563102`, build job `90436305353`, in `1m40s`.
