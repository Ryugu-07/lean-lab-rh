# H13 Dirichlet-Family Inclusion Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01`

Selected node: `H13-DIRICHLET-FAMILY-INCLUSION-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Selection reason

Campaign `FALSIFICATION-20260723-H2-HALF-ISOLATED-BOW-01` is publicly closed at final-ledger
commit `b13bc623e266990e9ba40802c6e1deb5ed87215a`, Lean Action run `29959903737`, build job
`89058172229`, in `2m14s`. The analytic half-isolated detector, actual-zeta bow exclusion, H2,
and RH remain open.

The historical atlas now has theorem-producing campaigns in H1, H2, H7/H8, H10, and H11, but
H13 generalized/automorphic L-functions and Iwasawa analogies has only a source card. Its exact
missing object is an individual transfer to every archimedean zeta zero. The highest-confidence
available transfer is not an analogy: the unique Dirichlet character modulo one has L-function
equal to the Riemann zeta function. Thus a family theorem containing that member must already
settle RH at that member.

This campaign tests that inclusion exactly and separately audits product enlargement. If a
generalized L-function contains zeta as a factor, critical-strip zero control for the product
implies RH. The reverse promotion is not automatic because an additional factor can insert a new
off-line critical-strip zero. This identifies directionality without claiming that generalized
families, Rankin--Selberg products, Dedekind zeta functions, or p-adic L-functions prove RH.

## Locked sources

1. Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`,
   `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`, especially
   `DirichletCharacter.LFunction_modOne_eq`, which states that every Dirichlet character modulo
   one has L-function equal to `riemannZeta`.
2. Stephen Gelbart and Stephen D. Miller, "Riemann's Zeta Function and Beyond," 2003,
   arXiv:math/0309478, especially the GL(1)/Hecke L-function discussion identifying the trivial
   character over Q with Riemann zeta.
   <https://arxiv.org/abs/math/0309478>
3. H. Davenport and H. Heilbronn, "On the Zeros of Certain Dirichlet Series," 1936. The existing
   source registry retains this as the historical obstruction showing that Riemann-type
   functional-equation structure without the appropriate Euler-product arithmetic can admit
   off-line zeros.
   <https://doi.org/10.1112/jlms/s1-11.4.307>

The Lean endpoint uses the first source's exact object. The abstract extra-factor witness is a
project falsification probe, not an implementation of the Davenport--Heilbronn series.

## Exact definitions

Define `criticalStripZerosOnLine f` for `f : Complex -> Complex` by

`forall s, f s = 0 -> InCriticalStrip s -> OnCriticalLine s`.

This deliberately controls only zeros in the open critical strip. It does not silently classify
trivial zeros or poles, and it does not assume that an arbitrary function is an L-function.

Define `allDirichletCriticalStripZerosOnLine` by quantifying this predicate over every modulus and
every Mathlib Dirichlet character at that modulus. Modulus one must be handled through the exact
`LFunction_modOne_eq` theorem, not through an informal identification.

Use an explicit factor such as `s - (1 / 4 : Complex)` for the product falsification. Its root is
inside the open critical strip and is not on the critical line.

## Fixed Lean endpoint

Create `LeanLab/Riemann/DirichletFamilyInclusionAudit.lean` and compile all of the following
without placeholders or resource relaxation:

1. Define the generic critical-strip-zero predicate and prove it is invariant under pointwise
   equality of functions.
2. Prove that `criticalStripZerosOnLine riemannZeta` is equivalent to Mathlib's
   `RiemannHypothesis`, including the conversion between critical-strip zeta zeros and the
   project's nontrivial-zero predicate.
3. Prove that the critical-strip claim for the unique Dirichlet L-function modulo one is
   equivalent to RH by `DirichletCharacter.LFunction_modOne_eq`.
4. Prove that the all-Dirichlet family claim implies RH by specializing to modulus one.
5. Prove a generic factor-inheritance theorem: if all critical-strip zeros of
   `fun s => riemannZeta s * g s` lie on the critical line, then RH holds.
6. Prove that the explicit product
   `fun s => riemannZeta s * (s - (1 / 4 : Complex))` fails the critical-strip-zero predicate.
7. Combine the exact family inclusion, one-way product transfer, and explicit reverse obstruction
   in an aggregate audit theorem.

Proposed declarations:

- `criticalStripZerosOnLine`
- `criticalStripZerosOnLine_riemannZeta_iff`
- `criticalStripZerosOnLine_dirichletL_modOne_iff`
- `allDirichletCriticalStripZerosOnLine`
- `riemannHypothesis_of_allDirichletCriticalStripZerosOnLine`
- `riemannHypothesis_of_criticalStripZerosOnLine_riemannZeta_mul`
- `not_criticalStripZerosOnLine_riemannZeta_mul_offLineFactor`
- `dirichletFamilyInclusionAudit_endpoint`

Names may change to fit namespaces, but the modulus-one specialization, open-strip hypotheses,
explicit off-line root, and implication directions may not be weakened silently.

## Success and falsification criteria

`FULL_SUCCESS` requires the exact zeta predicate equivalence, exact modulus-one Dirichlet
equivalence, all-family implication, generic product implication, explicit extra-factor
counterexample, aggregate endpoint, exact Targets and TargetChecks, selected standard-only axiom
prints, an empty production forbidden scan, full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires either the exact modulus-one equivalence or both the generic product
implication and explicit extra-factor obstruction, with the missing branch recorded precisely.

`TRANSFER_MISMATCH` occurs if Mathlib's modulus-one L-function equality cannot transport the
project's critical-strip predicate without additional analytic assumptions. Such assumptions must
be exposed rather than silently added.

## Claim boundary

- The all-Dirichlet claim is stronger than RH; proving its implication to RH is not a proof of the
  claim.
- The product theorem does not instantiate a Dedekind, Rankin--Selberg, or automorphic L-function.
- The explicit factor witness is not an Euler product and is not the Davenport--Heilbronn
  function.
- No family average, density theorem, p-adic interpolation theorem, main conjecture, or
  archimedean/p-adic zero map is proved.
- The campaign may close a transfer-logic node while leaving H13, every generalized RH, and RH
  open.

## Mechanical gates

Before proof-source editing:

- publish this preregistration and require public Lean Action CI;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register exact Targets and TargetChecks;
- print selected transitive axioms;
- scan the production module for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and
  `unsafe`;
- run `git diff --check`, the module build, full build, and public CI;
- retain the distinction between family inclusion, product factor inheritance, actual
  automorphic/Dedekind objects, generalized RH, and RH.

## Stop and successor rule

Stop this local campaign at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`, `TRANSFER_MISMATCH`, or proof
that the exact endpoint already exists. Local stop returns the persistent RH Goal to the unfinished
historical atlas. H13 remains open unless a proved generalized, automorphic, or p-adic mechanism
is transferred to every nontrivial zero of the individual Riemann zeta function. Original
conjectures and direct RH attacks remain open throughout.
