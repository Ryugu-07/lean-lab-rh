# H14 Finite-Height Promotion Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H14-FINITE-HEIGHT-PROMOTION-01`

Selected node: `H14-FINITE-HEIGHT-PROMOTION-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Selection reason

Campaign `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01` is publicly closed at
final-ledger commit `11822e34ad720b9715f7cc22d17e2ed066e51803`, Lean Action run
`29961935426`, build job `89064730187`, in `2m17s`. Generalized RH, actual automorphic or p-adic
individual-zeta transfer, H13, and RH remain open.

H14 certified finite computation is the remaining historical support route without an independent
campaign. Existing H11 work proves that density-one information can retain a fixed sparse off-line
exception, and H8 proves that eventual finite-index behavior need not be global. Neither theorem
has the exact finite-height quantifiers used by Turing-style zero verification.

This campaign therefore tests only the promotion step. For every finite height `T >= 0`, it will
construct a finite set of points in the open critical strip, closed under conjugation and
`s |-> 1-s`, such that every point with `abs(im) <= T` lies on the critical line while the set still
contains an off-line point above `T`. The witness is generic and is not an actual zeta zero set.

## Locked sources

1. Dave Platt and Tim Trudgian, "The Riemann hypothesis is true up to 3*10^12," 2020,
   arXiv:2004.09765. This supplies the audited finite-height statement and its valid use in a
   separate analytic de Bruijn--Newman reduction.
   <https://arxiv.org/abs/2004.09765>
2. D. H. J. Polymath, "Effective approximation of heat flow evolution of the Riemann xi function
   and a new upper bound for the de Bruijn--Newman constant," 2019, arXiv:1904.12438. This is the
   analytic consumer showing when a finite certificate can be decisive for a bounded endpoint.
   <https://arxiv.org/abs/1904.12438>

No numerical value from either source is optimized in this campaign.

## Exact abstraction

Define `verifiedOnCriticalLineUpTo zeros T` by requiring every `rho` in the finite set `zeros`
with `abs rho.im <= T` to satisfy `OnCriticalLine rho`.

For `T >= 0`, choose a base point with real part `1/4` and imaginary part `T+1`, then close it under
complex conjugation and `rho |-> 1-rho`. The four-point orbit lies in the open critical strip and
strictly above the certified height in absolute ordinate.

## Fixed Lean endpoint

Create `LeanLab/Riemann/FiniteHeightPromotionAudit.lean` and compile all of the following without
placeholders or resource relaxation:

1. Define the finite-height verification predicate.
2. Define the source-independent four-point orbit above a parameter height.
3. Prove the orbit is finite and nonempty.
4. Prove closure under conjugation and `rho |-> 1-rho`.
5. Prove every orbit point lies in the open critical strip.
6. Prove the finite-height verification predicate for every `T >= 0`.
7. Prove the orbit contains an off-line point whose absolute ordinate exceeds `T`.
8. Combine these properties into an existential theorem for every nonnegative finite height and an
   aggregate route-audit endpoint.

Proposed declarations:

- `verifiedOnCriticalLineUpTo`
- `finiteHeightAuditBase`
- `finiteHeightAuditOrbit`
- `finiteHeightAuditOrbit_conj_closed`
- `finiteHeightAuditOrbit_one_sub_closed`
- `finiteHeightAuditOrbit_inCriticalStrip`
- `finiteHeightAuditOrbit_verified`
- `finiteHeightAuditOrbit_has_high_offLine`
- `finiteHeightPromotionAudit_endpoint`

Names may change to fit Finset and Complex APIs, but the universal height quantifier, both source
symmetries, open-strip membership, and strict above-height off-line witness may not be weakened.

## Success and falsification criteria

`FULL_SUCCESS` requires all registered orbit properties, the universal existential theorem, exact
Targets and TargetChecks, selected standard-only axiom prints, an empty production forbidden scan,
full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires a finite symmetric witness for arbitrary nonnegative `T` that
passes finite-height verification and retains an off-line point, with any missing symmetry or
strip property recorded precisely.

`FINITE_PROMOTION_SURVIVES` occurs if the specified finite symmetric orbit cannot pass the exact
verification predicate while retaining an off-line point. That would falsify the witness design
and require re-examining the promotion logic.

## Claim boundary

- The finite orbit is not an actual zeta zero set and satisfies no Euler product or explicit
  formula.
- The theorem does not question the correctness or value of Platt--Trudgian's finite verification.
- The theorem does not refute finite computation paired with a separate global analytic reduction.
- No finite numerical bound is optimized.
- Closing the generic promotion node does not close H14 as a support tool and does not prove or
  disprove RH.

## Mechanical gates

Before proof-source editing, publish this preregistration and require public Lean Action CI while
keeping the six inherited protected files untouched and unstaged.

Before accepting any theorem, register exact Targets and TargetChecks, print selected transitive
axioms, scan the production module for forbidden constructs, run `git diff --check`, direct and
full builds, and public CI.

## Stop and successor rule

Stop this local campaign at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`, `FINITE_PROMOTION_SURVIVES`, or
proof that the exact endpoint already exists. Local stop returns the persistent RH Goal to the
historical atlas and conjecture pool. H14 remains available as a support tool whenever a proved
analytic theorem reduces an open global edge to a finite certificate. Original conjectures and
direct RH attacks remain open throughout.
