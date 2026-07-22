# H2 Half-Isolated Bow Geometry Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H2-HALF-ISOLATED-BOW-01`

Selected node: `H2-HALF-ISOLATED-BOW-GEOMETRY-01`

Status: `EVIDENCE_CI_PASSED / FINAL_LEDGER_REQUIRED`

Preregistration commit `1475d90b96f6a5aabf9a6afea72a56575f11dc61` passed public Lean Action
run `29958359541`, build job `89053021275`, in `1m48s`. Proof-source editing began only after this
gate passed.

Frozen implementation commit `2cac0b4813435dffe468cd87f888d9f2763263d9` passed public Lean
Action run `29959216007`, build job `89055884594`, in `2m11s`. Lean proof source is frozen;
immutable-evidence commit `5f9f8ea175c269507e96fbb0a8ca8dff40144e12` then passed public Lean
Action run `29959619394`, build job `89057229832`, in `1m30s`. The generic geometry audit has
reached its registered local stop. Final-ledger publication and CI precede fresh historical-route
selection; the analytic detector, actual-zeta bow exclusion, H2, and RH remain open.

## Selection reason

H10-C final-ledger commit `2edf069a217255bbc20b93a2aa938f51dd57d94e` passed public Lean
Action run `29957374602`, build job `89049724940`, in `1m54s`. Its literal infinite ordinary-trace
audit is closed while regularized traces, H10, and RH remain open.

Fresh cross-family comparison found that H1 mollifiers, H7/H8 spectral and entire-function
geometry, H10 function-field transfer, and H11 zero statistics now have theorem-producing public
campaigns. H2 zero density and large values remains a canonical family without an independent
attempt. The existing H2 card records Guth--Maynard's exponent but omits Maynard--Pratt's
vertically sensitive half-isolated-zero detector and its explicit bow obstruction.

This campaign therefore audits the source geometry rather than optimizing a density exponent. It
asks whether finite vertical-line rigidity is genuinely used to extract an off-line half-isolated
zero, and whether functional-equation reflection symmetry alone can replace that rigidity.
Original conjectures and direct RH attacks remain open throughout.

## Locked sources

1. James Maynard and Kyle Pratt, "Half-isolated zeros and zero-density estimates," IMRN 2024,
   arXiv:2206.11729v2, especially Definitions 9 and 12, Lemma 16, and Section 8.
   <https://arxiv.org/abs/2206.11729>
2. Larry Guth and James Maynard, "New large value estimates for Dirichlet polynomials,"
   arXiv:2405.20552v2, especially the Type-I/Type-II zero-detecting reduction in the proof of the
   zero-density theorem.
   <https://arxiv.org/abs/2405.20552>

Maynard--Pratt define a `Y`-half-isolated zero by requiring every nearby zero either to have very
similar real part and no smaller ordinate, or to lie a prescribed distance to the left. Under the
finite-vertical-line Hypothesis F, clusters have a bottom half-isolated zero. Without real-part
rigidity, Section 8 gives bow configurations as the obstruction to the local power-sum detector.
The source proves that half-isolated zeros are sparse; it does not prove that no such zero exists.

## Exact geometric abstraction

For a local zero set `S`, radius `r`, similar-real-part tolerance `delta`, and left-gap threshold
`Delta`, define `halfIsolatedIn S r delta Delta rho0` by the literal source disjunction:

1. every `rho in S` with `dist rho rho0 <= r` satisfies
   `abs (rho.re - rho0.re) <= delta` and `rho0.im <= rho.im`; or
2. `rho.re <= rho0.re - Delta`.

The logarithmic source scales are parameters rather than silently replaced by numerical values.
The critical-line reflection on the upper half-plane is `rho |-> 1 - conj rho`.

## Fixed Lean endpoint

Create `LeanLab/Riemann/HalfIsolatedBowAudit.lean` and compile all of the following without
placeholders or resource relaxation:

1. Define the exact local half-isolation predicate and critical-line reflection.
2. Prove a source-shaped positive criterion: if `rho0` is rightmost in `S`, every other real part
   is either equal to `rho0.re` or at least `Delta` to its left, and `rho0` has the least ordinate
   on its vertical line, then `rho0` is half-isolated for every radius and every nonnegative
   similar-real-part tolerance.
3. Construct a finite nontrivial set invariant under critical-line reflection with a point to the
   right of the critical line, but with no right-half-plane point half-isolated. The blocker must
   be a nearby lower point whose real-part displacement lies strictly between `delta` and `Delta`.
4. Prove explicitly which vertical-gap premise the finite bow violates; do not classify the
   witness as a zeta zero set.
5. Combine the positive finite-line criterion and the symmetry-only countermodel in one aggregate
   route-audit theorem.

Proposed declarations:

- `halfIsolatedIn`
- `criticalLineReflect`
- `halfIsolatedIn_of_rightmost_bottom_and_verticalGap`
- `finiteBow_is_reflectionInvariant`
- `finiteBow_has_offLinePoint`
- `finiteBow_no_right_offLine_halfIsolated`
- `halfIsolatedBowAudit_endpoint`

Names may change to fit Mathlib's complex and finite-set APIs, but the source disjunction,
critical-line reflection, strict intermediate real-part displacement, and universal failure for
right-side points may not be weakened silently.

## Success and falsification criteria

`FULL_SUCCESS` requires the positive vertical-rigidity theorem, the reflection-invariant finite
bow countermodel, exact Targets and TargetChecks, selected standard-only axiom prints, an empty
production forbidden scan, full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires either the exact positive criterion or a symmetry-invariant
countermodel using the full source-shaped disjunction, with the missing half recorded precisely.

`SYMMETRY_FORCES_DETECTION` requires proof that no finite reflection-invariant countermodel can
exist under the locked parameter inequalities. That result would falsify the proposed bow witness
and reopen the geometry as a possible omitted rigidity mechanism.

## Claim boundary

- No actual zeta zero, multiplicity, zero-count function, or Dirichlet polynomial is formalized.
- The finite witness is not asserted to satisfy the Euler product, explicit formula, or local zero
  statistics of zeta.
- No result reproves Maynard--Pratt's analytic short-detector theorem or Guth--Maynard's large-value
  estimate.
- A symmetry-only countermodel does not show that actual zeta bows exist.
- Closing this generic geometry does not close H2, exclude a stronger bow-rigidity theorem, or
  prove RH.

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
- retain the distinction between finite geometry, actual zeta zero detection, zero-density bounds,
  and zero exclusion.

## Stop and successor rule

Stop this local campaign at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`,
`SYMMETRY_FORCES_DETECTION`, or proof that the exact endpoint already exists. Local stop returns
the persistent RH Goal to the unfinished historical atlas. H2 remains open unless the actual bow
obstruction is excluded and the analytic detector is upgraded from a density bound to zero
exclusion. Original conjecture and direct RH attempts remain open.
