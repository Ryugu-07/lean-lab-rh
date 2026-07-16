# H6 de Bruijn Upper-Half Campaign

Campaign: `CAMPAIGN-20260717-H6-UPPER-HALF-01`

Mode: `LITERATURE`

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: resumed after public closure of H6-H2c; canonical governance, HANDOFF,
  Targets, the hard-gap DAG, H6 route card, source registry, and the completed forward campaign
  were reread from the repository
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: for `0 <= t <= 1/2`, every zero of `H_t` satisfies
  `Im(z)^2 <= 1-2*t`; hence every zero of `H_(1/2)` is real.
- `proposed_Lean_statements`: `deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul` and
  `deBruijnNewmanAllZerosReal_one_half`.
- `relation_to_RH`: proves the classical positive upper-time witness and threshold nonemptiness.
  It does not prove `deBruijnNewmanAllZerosReal 0`, which remains RH-equivalent.
- `success_criterion`: both exact endpoints plus every witness, trust, build, and public CI gate in
  `research/h6_upper_half_prereg_20260717.md`.
- `falsification_criterion`: the paired-factor contraction, multiplicity involution, factor of two,
  finite strip invariant, or limit persistence fails for the source normalization.
- `assumption_frontier_before`: exact source integral, order-one entire heat family, strict
  time-zero strip, closed good-time set, forward preservation, vertical averages, heat-multiplier
  convergence, and Jensen persistence are public.
- `hard_gap_before`: threshold nonemptiness/upper-time existence, H6-E/G8, W2/G7, M2/G3, and RH
  are open.
- `known_obstacle`: mathlib has no Laguerre-Polya or strip-preserver class. The multiplicity-bearing
  Hadamard divisor has no conjugation involution, and the prior product comparison applies only
  when every root is real.
- `nearest_primary_source`: de Bruijn 1950; Rodgers-Tao arXiv `1801.05914`; Branden-Chasse arXiv
  `1402.2795`.
- `nearest_project_attempt`: H6-H2c proves the zero-width vertical-average theorem and the exact
  heat limit. It cannot be applied at time zero because that would assume RH.
- `new_attack_angle`: generalize the compiled factor comparison from single real factors to
  conjugate factor pairs, carry a squared strip-width invariant through the existing finite
  `cosh` iteration, and reuse the already kernel-checked limit argument.

## Route-selection loop

- Re-read the canonical V4.1 governance and current project state after the H6-H2c closure.
- Compared direct H6-E, W2, and M2 re-entry, the numerical `0.22`/`0.2` frontier, threshold
  definition packaging, and the classical half-time theorem.
- Found no materially new unconditional positivity or approximation mechanism for the three
  direct hard gaps.
- Rejected threshold-definition packaging before nonemptiness as bookkeeping rather than the
  next mathematical frontier.
- Deferred `0.22` and `0.2`: both require substantially more effective and numerical
  certification infrastructure than the classical source theorem.
- Confirmed in Rodgers-Tao that the exact source normalization is all-real-zero for `t >= 1/2`.
- Confirmed in Branden-Chasse the shifted strip contraction by `a^2` and heat contraction by
  `2*t`, including the finite-order entire extension.
- Audited the compiled H6-H2c proof and found reusable order-one factorization, vertical-average
  iteration, scaled `cosh` limit, error majorant, and Jensen persistence.
- Identified the first genuinely new dependency as conjugate-pair comparison on the
  multiplicity-bearing Hadamard divisor.
- `result`: select H6-H2d; public preregistration gate pending.
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Current decision

- `public_preregistration`: commit `502864b4a84740600c80a4864f3a3e3deb331c46`, Lean Action CI
  run `29528426983`, build job `87722558836`, passed in `1m50s`.
- `route_selection_decision`: begin the fixed implementation with conjugation multiplicity and
  paired-factor contraction, without weakening either endpoint.
- `campaign_status`: public preregistration verified; implementation active; persistent RH Goal
  remains active.

## Implementation loops

| Loop | State | Compiler-checked result | Decision |
| --- | --- | --- | --- |
| 1 | `CONJUGATION_MULTIPLICITY` | Proved source conjugation symmetry, iterated-derivative symmetry, equality of analytic zero orders under conjugation, and a multiplicity-bearing divisor involution. | Continue to the fixed paired-factor obstruction. |
| 2 | `PAIRED_FACTOR_ALGEBRA` | Proved strict lower/upper shift comparison for the product of the genus-one factors at `r` and `conj(r)`. The numerator difference is `8*a*Im(z)*((Re(r)-Re(z))^2+Im(z)^2+a^2-Im(r)^2)`; exponential norms cancel. | Lift from one pair to the full divisor product. |
| 3 | `INFINITE_PRODUCT_PAIRING` | Initial concrete-equivalence reindexing exceeded deterministic heartbeats because the dependent divisor equivalence unfolded repeatedly. Factoring the argument into `norm_tprod_lt_norm_tprod_of_equiv_pairing` made the equivalence opaque and compiled under default limits. | Retain the generic helper; no resource relaxation. |
| 4 | `ONE_STEP_STRIP` | Proved `verticalAverage_zero_im_sq_le`, including empty divisors, real fixed roots, nonzero upper product, and both half-planes. | Establish every finite-stage nonvanishing premise independently. |
| 5 | `FINITE_ITERATION` | Proved strict positivity of `dbnCoshApprox t a n 0`, then order-one, evenness, conjugation, and the invariant `Im(z)^2 <= 1-n*a^2`. For `a=sqrt(2*t/n)` this becomes exactly `1-2*t` for every `n>0`. | Transfer the closed strip to the heat limit. |
| 6 | `LIMIT_PERSISTENCE` | Built an isolating closed ball wholly outside the contracted strip and reused compact-uniform error control plus Jensen's circle mean to force a late approximant zero in that ball. | Contradict the finite-stage strip and close both endpoints. |
| 7 | `INDEPENDENT_LOCAL_AUDIT` | Exact module, Targets, TargetChecks, eight standard-only axiom prints, empty forbidden/resource scans, `git diff --check`, and the 8,690-job full build pass. | Publish implementation and require public CI. |

## Local result

- `exact_endpoint`: `deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul` compiles for the full fixed
  interval and exact width `1-2*t`; `deBruijnNewmanAllZerosReal_one_half` compiles unconditionally.
- `axiom_status`: every registered witness and endpoint prints exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- `sorry_or_unchecked_declaration_used`: no.
- `assumption_frontier_after`: the exact good-time set is compiled as nonempty, with witness
  `t=1/2`; combined with H6-H2b/H2c it contains the closed upper ray from that witness.
- `hard_gap_after`: H6-E/G8 (`Lambda<=0`), W2/G7, M2/G3, and RH remain open.
- `hard_gap_delta`: 0.
- `route_infrastructure_delta`: 1.
- `classification`: `KNOWN_THEOREM_FORMALIZED`; this reconstructs de Bruijn's classical theorem
  and makes no originality claim.
- `next_gate`: implementation commit and public Lean Action CI, then immutable evidence backfill
  and closure CI. The persistent RH Goal remains active throughout.

## Public implementation result

Implementation commit `8669c2db7577eaa718684e9e9ec052062b5488fa` passed public Lean Action CI
run `29531232787`, build job `87731748374`, in `2m6s`. Both fixed endpoints and the complete
registered proof chain are now independently public-built. The campaign remains active at
`PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`; immutable evidence backfill and its own public
CI are required before closure.
