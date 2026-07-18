# H6 Polymath Zero-Free-Region Criterion Campaign

Campaign: `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`

Date: 2026-07-17

Status: `LOCAL_SUCCESS_PENDING_PUBLIC_CI`

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
- `known_obstacle`: closed for the formalized criterion. Compact-uniform Hermite scaling, zero
  transfer, repeated-contact escape, the strict canopy, and all three exact conditional endpoints
  compile. The new external frontier is the three separately stated numerical region certificates.
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
| 7 | `PROOF-ATTEMPT` | Added the source-normalized backward Hermite family `P_0=1`, `P_(n+1)=X*P_n+2*P_n'`. Lean proves coefficient nonnegativity, exact degree and monicity, parity vanishing, strict positivity of the even constant and odd linear coefficients, `P_n(-X)=(-1)^n P_n(X)`, positivity on the positive real axis, and exclusion of every nonzero real root. Algebraic closedness then gives a nonzero root directly for even degree and through `P_n.divX` for odd degree; negation places a root strictly in the upper half-plane. The exact theorem `exists_deBruijnNewmanBackwardHermite_aeval_eq_zero_im_pos` compiles for every `n>=2`. Exact TargetCheck and three selected axiom prints pass with only `propext`, `Classical.choice`, and `Quot.sound`. This proves the finite splitting model, not its realization by actual heat-family zeros. Implementation commit `7ac27aa86cd176ef6172b79b3b854724b1243f7a` passed public CI run `29582740550`, job `87892131096`, in `2m05s`. | Keep the campaign active. The next exact gate is a compact-uniform `sqrt(t-s)` scaled limit from a repeated source-family zero to a nonzero scalar multiple of `P_m`, followed by a zero-transfer theorem in a small disk around a strict upper-half-plane model root. Only then may the linear-escape interface be claimed. |
| 8 | `PROOF-ATTEMPT` | Lean now extracts a finite analytic multiplicity `m>=2` at every repeated source zero and upgrades the local Taylor factor to a global entire factor `H_t(w)=(w-z)^m g(w)` with `g(z)!=0`, using iterated `dslope` and the analytic identity theorem. A new sharp strip estimate `norm(cos w)<=exp(abs(w.im))`, the variance-two Gaussian characteristic function, and the existing theta-kernel majorant prove product integrability and the exact semigroup identity `integral H_t(w+r*y) d gaussianReal(0,2)=H_(t-r^2)(w)`. Combining both gives the exact all-scale representation `H_(t-r^2)(z+r*xi)=r^m integral (xi+y)^m g(z+r*(xi+y)) d gaussianReal(0,2)`. The source file, exact TargetChecks, four selected axiom prints, forbidden scans, `git diff --check`, and the full 8,703-job build pass locally; all selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Implementation commit `549b35e736b9a2de02282bd8ac41bf010b858196` passed public CI run `29626216475`, job `88031047702`, in `2m15s`. | Keep the campaign active. The former local-factor/Fubini gap is closed. Next prove that the Gaussian moment polynomial is exactly the compiled backward Hermite `P_m`, establish compact-uniform convergence of the residual factor to `g(z)`, and transfer one strict upper-half-plane model root to an actual zero. Do not claim backward upper linear escape before that transfer compiles. |
| 9 | `PROOF-ATTEMPT` | Lean identifies every shifted centered variance-two Gaussian moment with the compiled backward Hermite polynomial: `integral (xi+y)^n d gamma_2 = P_n(xi)`. The proof uses the closed Gaussian complex MGF, an iterated-derivative formula for `exp(s*xi+s^2)`, the exact Leibniz sum, finite-moment integrability, and no coefficient guesswork. The source family is now proved uniformly bounded on every horizontal strip; a global residual factor inherits this bound by compactness near the divided-out zero and factorization away from it. This supplies an explicit Gaussian-integrable domination and proves joint continuity of the scaled residual integral at every `(0,xi)`, hence the exact pointwise limit to `P_m(xi)*g(z)`. | Keep the campaign active. Loop 10 must upgrade joint continuity to compact-uniform convergence on a disk around a strict upper-half-plane model root, then prove a zero-transfer theorem and finally derive `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`. No Polymath endpoint or RH claim is made. |
| 10 | `PROOF-ATTEMPT -> LOCAL_SUCCESS` | Lean upgrades the scaled residual integral to compact-uniform convergence by applying compact-set uniform continuity to the zero-scale fiber `{0} x K`. It isolates a backward Hermite root in a closed disk satisfying `xi.im > rho.im/2`, proves a generic Jensen minimum-modulus zero-transfer lemma, and obtains an actual scaled heat zero for every sufficiently small nonzero scale. The square-root displacement gives `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`. Combining this with first-contact minimality closes the strict canopy, the exact `t0+y0^2/2` all-real theorem, and the Table 1 row at `1/5`. Exact TargetChecks and selected axiom prints pass; all selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`. | Mark the campaign locally successful pending full gates and public implementation/evidence CI. Do not claim any of the three region predicates, unconditional `Lambda<=0.2`, H6-E/G8, or RH. |

Loop 10 local gates passed for both source modules, Targets, exact TargetChecks, six new selected
axiom prints, forbidden placeholder/declaration/resource/scratch scans, `git diff --check`, and the
full 8,703-job build. Every selected new declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`. Public implementation and evidence CI remain pending.

Loop 9 local gates passed for the source module, Targets, exact TargetChecks, four selected axiom
prints, forbidden scans, `git diff --check`, and the full 8,703-job build. The selected declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. Implementation commit
`5e90f7ee9648a55fd10c2ea244741e2fc3254039` passed public Lean Action CI run `29627444553`, build
job `88034514707`, in `2m15s`.

## Compiled Closure

The simple-contact force branch is now compiled end to end. In particular,
`deBruijnNewmanPolymath_firstBadWitness_not_simple` derives repeated contact directly from the
three region certificates and first-time minimality; it does not assume the force inequality.

The repeated branch now supplies the exact theorem shape

```lean
theorem deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated
    {t : Real} {z : Complex}
    (hz : deBruijnNewmanH t z = 0)
    (hrepeated : deriv (deBruijnNewmanH t) z = 0) :
    deBruijnNewmanHasBackwardUpperLinearEscape t z
```

Loop 10 proves compact-uniform convergence on every compact set, isolates an upper-half-plane
model root with a uniform imaginary margin, transfers a zero by Jensen's circle-average theorem,
and handles the full left-neighborhood quantifier using `r=sqrt(t-s)`. The compiled criterion
endpoints are:

- `deBruijnNewmanH_zero_im_abs_lt_of_polymath_regions`;
- `deBruijnNewmanAllZerosReal_add_half_sq_of_polymath_regions`;
- `deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_row`.

Each remains conditional on the three exact region predicates. No numerical certificate is
silently imported.

## Current Accounting

- `hard_gap_before`: the initial, final, and barrier region certificates, H6-E/G8, and RH open
- `hard_gap_after`: unchanged
- `hard_gap_delta`: 0
- `classification`: `KNOWN_THEOREM_FORMALIZED_LOCAL_SUCCESS`
- `next_gate`: full local gates, public implementation CI, evidence backfill CI, then return to
  value-ranked RH route selection; the three numerical region certificates remain independent
  open candidates
- `persistent_goal`: active
