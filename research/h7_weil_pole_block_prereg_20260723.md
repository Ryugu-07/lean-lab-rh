# H7 Weil Pole Block Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H7-WEIL-POLE-BLOCK-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Selected node: `H7-WEIL-POLE-RANK-TWO-INSTANTIATION-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `b3c967d64a7c9df3cec8c251a302190e516aad81`.
- `parent_public_ci`: Lean Action run `29969901015`, build job `89089454873`, passed in `2m0s`.
- `route_selection`: `research/route_selection_post_h1_bettin_gonek_auxiliary_20260723.md`.
- `nearest_h7_modules`: `WeilGroundStateAlignment`, `WeilGroundStateFiniteMatrix`,
  `WeilGroundStateHerglotz`, and `WeilGroundStateRayleighGap`.
- `global_goal`: active.

## Locked sources

1. Groskin, arXiv:2607.02828, Section 2, especially the source pole function and entry
   identification lemma.
2. Connes--Consani--Moscovici, arXiv:2511.22755, Lemma 4.1 and the finite-prime Weil matrix.
3. Andrade, June 2026 scalar Herglotz note, for the parity rank-one interpretation only.

The first source gives

```text
beta = log(c)/(4*pi),
C_c = log(c)*(sqrt(c)+1/sqrt(c)-2)/(2*pi^2),
psi_0(k) = C_c*k/(k^2+beta^2),
psi_0'(k) = C_c*(beta^2-k^2)/(k^2+beta^2)^2.
```

Its divided-difference matrix is claimed to equal

```text
C_c*(beta^2-m*n)/((m^2+beta^2)*(n^2+beta^2)).
```

## Fixed Lean endpoint

Only after this preregistration passes public CI, create
`LeanLab/Riemann/WeilGroundStatePoleBlock.lean` and compile without placeholders or resource
relaxation:

1. Define the exact source `L`, `beta`, and `C_c`, and prove `beta>0` and `C_c>0` for `c>1`.
2. Define the centered source value and derivative samples and prove odd/even reflection parity.
3. Define the source divided-difference pole matrix through
   `weilFiniteDividedDifferenceMatrix`.
4. Prove the all-entry closed formula, including the diagonal and off-diagonal cases.
5. Define the exact even and odd pole vectors and prove their reflection parity.
6. Prove the exact matrix decomposition
   `Q_pole=C_c*(vecMulVec e e-vecMulVec o o)`.
7. Prove for every finite real vector `x` the exact quadratic identity
   `x dot (Q_pole*x)=C_c*((e dot x)^2-(o dot x)^2)`.
8. Prove the even-sector nonnegativity and odd-sector nonpositivity laws, with their exact square
   formulas.
9. Register one proven source-block Target, exact TargetChecks, selected axiom prints, and an
   aggregate endpoint theorem.

Names may change to fit checked Mathlib APIs, but the source coefficient, both rank-one signs,
and the all-vector quadratic identity may not be weakened.

## Claim boundary

This campaign does not define the prime or archimedean source blocks, assemble the total Weil
matrix, prove either sector positive for the total matrix, prove the Herglotz scalar inequality,
prove simple-even ground-state structure, compare a true ground state to the prolate vector,
establish transform convergence, or prove RH. The pole block alone has opposite signs on the two
parity sectors and is not a positivity theorem for the complete explicit formula.

No open H7 statement may be used as a premise. The June 2026 scalar inequality and all numerical
tables remain navigation evidence only.

## Outcome rule

- `FULL_SUCCESS_AT_POLE_ENDPOINT`: all nine fixed items compile with exact source normalization.
- `SOURCE_NORMALIZATION_MISMATCH`: the source divided difference differs from the displayed
  closed formula or rank-two coefficient after exact algebra.
- `MEANINGFUL_PARTIAL`: the exact matrix formula compiles but a named finite-matrix API gap blocks
  the all-vector quadratic identity or parity sign law.
- `NO_PROGRESS`: the source object cannot be represented without changing its matrix entries.

Stop at one outcome. Success returns the actual prime/archimedean blocks and the Herglotz scalar
bound to cross-route value ranking; failure records the precise formula obstruction. Closing this
campaign does not exhaust D6.

## Mechanical gates

Publish this preregistration and require public Lean Action CI before creating the production
module. Then require no-sorry production source, exact Targets and TargetChecks, selected
transitive axiom prints, an empty forbidden scan, direct compiles, `git diff --check`, a full
build, frozen implementation CI, immutable evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

## Runtime disclosure

- Model: Codex, GPT-5 family; exact serving variant not exposed.
- Reasoning effort: not exposed.
- Numerical loop quota: none under V4.1; serving token budget not exposed.
- Compaction: one inherited summary was used to resume and publicly close the H1 auxiliary
  campaign. The current H7 alignment, finite-matrix, Herglotz, Rayleigh-gap records and the locked
  source formulas were re-read before this selection.
