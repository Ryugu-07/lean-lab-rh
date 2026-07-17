# H6 Polymath Zero-Free-Region Criterion Campaign

Campaign: `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`

Date: 2026-07-17

Status: `ACTIVE_PROOF_ATTEMPT`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes; resumed from the canonical campaign summary after
  preregistration

## Normalized Tuple

- `statement`: the complete Polymath three-region zero-free criterion, its exact
  `t0+y0^2/2` all-real endpoint, and the Table 1 second-row corollary at time `1/5`
- `assumptions`: only the three explicit source region predicates and positivity constraints on
  `t0`, `X`, and `y0`; standard Mathlib analysis and compiled source-normalized H6 infrastructure
- `strategy`: compact first-contact time, repeated-zero backward Hermite splitting,
  arbitrary-complex simple-zero force geometry, and general strip contraction
- `known_obstacle`: the arbitrary-complex simple-zero path, compact first contact, divisor-orbit
  strict imaginary force inequality, and complete simple-contact contradiction now compile. The
  sole remaining source dependency is repeated-zero backward Hermite splitting.
- `nearest_primary_source`: Polymath arXiv `1904.12438`, Proposition 3.3, Theorem 1.2, and Table 1;
  Platt--Trudgian arXiv `2004.09765`, Corollary 2
- `nearest_project_attempt`: H6-H2e supplies only the final strip contraction; the zero-dynamics
  campaign supplies simple real paths and the regularized force but explicitly leaves repeated
  zeros and global continuation open
- `new_attack_angle`: use a compact first-contact set and complete both source collision branches,
  rather than assume a global strip or continue only real simple zeros

## Loop Ledger

| Loop | Mode | Result | Decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION -> LITERATURE` | Compared H6-Q, strict-below-0.2, W2, M2, H1/H2 counts, and H10. Primary-source review identifies Polymath Proposition 3.3 as the first structural consumer of the newly compiled general strip theorem. It requires real new analysis: compact first contact, repeated-zero Hermite splitting, and complex simple-zero force geometry. | Preregister the complete criterion and exact table-row corollary; require public CI before proof edits. |
| 2 | `LITERATURE -> PROOF-ATTEMPT` | Public preregistration CI passed at commit `8f9425edd6257011b4beea644196053d9ca86d73` (run `29573972608`, job `87864082110`, `2m02s`). API audit shows that the arbitrary-complex simple-zero path can be extracted directly from the existing joint implicit-function proof. No existing Mathlib or project theorem supplies the repeated-zero backward Hermite splitting required at first contact. | Open the proof-source gate. Compile the arbitrary-complex simple-zero path first, then isolate the exact repeated-zero persistence/splitting lemma before attempting the global contact argument. |
| 3 | `PROOF-ATTEMPT` | Exported `exists_deBruijnNewman_localComplexSimpleZeroPath` from the existing product-domain implicit-function proof and refactored the real path through it. Defined all three closed Polymath regions. Proved strict positivity and nonvanishing on the entire imaginary axis, and proved that the source strip bound removes all three regional upper-height clauses. | Continue to a compact first-contact construction; do not introduce a global zero enumeration. |
| 4 | `PROOF-ATTEMPT` | Proved compactness of the bounded spacetime witness set and its bad-time projection, existence and positivity of the first bad time, exclusion of both vertical sides, and exact contact with the moving lower boundary. The proof uses the exported arbitrary-multiplicity isolating-ball persistence theorem. Compiled both branch consumers: the strict force inequality rules out a simple contact, while minimality rules out `deBruijnNewmanHasBackwardUpperLinearEscape`. Also compiled the strict-canopy-to-strip bridge and exact Table 1 arithmetic to time `1/5`. Full local build and selected axiom audit passed. Implementation commit `b4c2f5e24ab35514dccf0f6d85ff40ce43e026c3` passed public CI run `29576156216`, job `87870943510`, in `3m35s`. | Checkpoint the infrastructure. Attack the force inequality first by averaging the absolutely convergent regularized divisor sum over the `z -> -z` and conjugation orbit; keep Hermite escape as an independent exact obstruction. |
| 5 | `PROOF-ATTEMPT` | Publicized the multiplicity-preserving conjugation divisor equivalence, proved the corresponding negation equivalence from analytic-order invariance, and exposed the regularized force `tsum`. Proved the abstract quarter-of-four-orbits reindexing identity and specialized it to `deBruijnNewmanRegularizedZeroForce`. For non-contact orbits, regularization cancels exactly; the source cross-multiplication inequality, the two conjugate-pair estimates, the fourfold imaginary nonpositivity theorem, and the strip-or-horizontal-escape geometry all compile. For a contact representative, the exact orbit sum compiles as `-1/(2r) + 1/(r-conj r) + 1/(r+conj r)`. Implementation commit `90fdf2b9039da2a9cdb07758b3a24ab335958018` passed public CI run `29578060529`, job `87876981475`, in `2m55s`. | Isolate the four contact divisor indices using the simple fiber cardinality and their pairwise-distinct values; remove that finite set from the summable imaginary orbit series, prove the complement `tsum` nonpositive, and close the strict force inequality. |
| 6 | `PROOF-ATTEMPT` | Made the simple-zero divisor fiber cardinality public. Proved the contact symmetry orbit has exactly four indices, the orbit term is invariant under both generators, and its finite sum is four times the contact term. Removed this Finset from the absolutely convergent imaginary `tsum`; every complementary orbit is nonpositive, yielding `deBruijnNewmanRegularizedZeroForce_im_lt_of_simple_contact_escape`. Proved every divisor zero has a first-quadrant symmetry representative. At the earliest bad time, boundary rigidity excludes higher zeros with `|Re|<=X`, while the barrier excludes the following horizontal buffer; this supplies the force theorem's escape premise. The compiled theorem `deBruijnNewmanPolymath_firstBadWitness_not_simple` therefore closes the complete simple-contact branch from the three region certificates. Exact TargetChecks and seven selected axiom prints pass with the standard trust base only. Implementation commit `cedbd4d92dcdd05d76b868a95d6fcb2479a3db96` passed public CI run `29580228443`, job `87883895459`, in `2m33s`. | Keep the campaign active. Attack the sole remaining source interface: repeated-zero backward Hermite splitting strong enough to imply `deBruijnNewmanHasBackwardUpperLinearEscape`; do not claim the final criterion before that interface compiles. |

## Exact Remaining Source Interface

The simple-contact force branch is now compiled end to end. In particular,
`deBruijnNewmanPolymath_firstBadWitness_not_simple` derives repeated contact directly from the
three region certificates and first-time minimality; it does not assume the force inequality.

The repeated branch must supply the exact theorem shape

```lean
theorem deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated
    {t : Real} {z : Complex}
    (hz : deBruijnNewmanH t z = 0)
    (hrepeated : deriv (deBruijnNewmanH t) z = 0) :
    deBruijnNewmanHasBackwardUpperLinearEscape t z
```

or a stronger Hermite asymptotic theorem implying it. Jensen persistence without a scaled
Hermite limit is insufficient: it preserves a nearby zero but gives no one-sided imaginary
displacement.

## Current Accounting

- `hard_gap_before`: the initial, final, and barrier region certificates, H6-E/G8, and RH open
- `hard_gap_after`: unchanged
- `hard_gap_delta`: 0
- `classification`: `ACTIVE_PROOF_ATTEMPT_CHECKPOINT`
- `next_gate`: repeated-zero backward Hermite splitting implying
  `deBruijnNewmanHasBackwardUpperLinearEscape`
- `persistent_goal`: active
