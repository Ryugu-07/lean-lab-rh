# R3 Reverse Li Criterion Campaign

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-LI-REVERSE-BOMBIERI-LAGARIAS-01`

Route: R3, Li and Weil positivity

Status: `CLOSED_PUBLIC_CI_VERIFIED`

Fixed endpoint and admission conditions:
`research/r3_li_reverse_bombieri_lagarias_prereg_20260715.md`.

## Attempt A

The admitted attempt was the complete project-specialized Bombieri--Lagarias contradiction:

1. characterize the norm of `q(rho)=1-1/rho` by the half-plane containing `rho`;
2. package the reflection-invariant radius `max |q| |q^-1|` and prove it exceeds one off-line;
3. prove every radius superlevel above one is finite;
4. choose the dominant member of each reciprocal pair and normalize it to `Complex.Circle`;
5. return all phases in a finite superlevel set simultaneously near one at arbitrarily large even
   powers;
6. bound each aligned main term by `3/2-(3/8)R^m`;
7. dominate the complement by `m^2*c^m` times one fixed summable reciprocal-square weight;
8. derive a negative project Li coefficient from any off-line divisor zero;
9. contradict all-index nonnegativity and close the exact RH equivalence.

No helper alone counted as a result.

## Attempt A Refinement

The preregistered source reconstruction used a globally maximal transformed zero and a far/near
split. The Lean proof found a shorter equivalent specialization. Given one off-line orbit with
radius `R0>1`, set `c=(1+R0)/2`. The set of all divisor indices with radius at least `c` is finite,
contains the chosen orbit, and is phase-aligned in full. Every index outside it has radius below
`c`, so the pointwise paired estimate and the globally summable reciprocal-square weight give the
whole complement bound directly. Since `c<R0`, the standard polynomial-versus-exponential limit
makes this tail smaller than the distinguished negative term. No maximum, zero enumeration, zero
counting estimate, or index-dependent near set is needed.

## Lean Result

`LeanLab/Riemann/LiReverseCriterion.lean` compiles the complete chain.

- `exists_even_gt_forall_circle_pow_dist_one_lt` proves simultaneous finite phase recurrence by
  compact subsequences in a finite product of circles.
- `norm_liZeroTransform_le_one_iff` proves the exact transform/half-plane geometry.
- `finite_riemannXiLiOrbitRadius_superlevel` proves every radius threshold above one is finite.
- `norm_tsum_indicator_compl_riemannXiSymmetrizedLiZeroTerm_le` gives the full complement bound by
  one fixed summable weight.
- `exists_liCoefficientCandidate_re_neg_of_divisorZero_re_ne_half` turns any off-line divisor zero
  into a strictly negative Li coefficient.
- `riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg` is the reverse criterion.
- `riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg` is the exact all-index iff.

The project index remains classical `lambda_(n+1)`.

## Verification

- Standalone `rtk lake env lean LeanLab/Riemann/LiReverseCriterion.lean`: passed without warnings.
- Integrated module/Targets/TargetChecks/AxiomsAudit build: passed, 8,657 jobs.
- Exact reverse and iff statement witnesses in `TargetChecks`: passed.
- Eight selected declarations in `AxiomsAudit` use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Full `rtk lake build`: passed, 8,661 jobs; replayed warnings are confined to pre-existing files.
- Placeholder, explicit axiom, `native_decide`, unsafe/opaque declaration, and resource-relaxation
  scans are empty.
- `rtk git diff --check`: passed.
- Implementation commit `22cedfa17788fec546b91b9dc78452de52d87e64` is public on `main`.
- Lean Action CI run `29406614212`, build job `87323510543`, succeeded in 2m31s.
- Evidence-backfill commit `48385f277c83b06a5d72aee83d06d0f4b31623d1` is public on `main`.
- Lean Action CI run `29406932411`, build job `87324549428`, succeeded in 1m21s.

## Progress Accounting

Result: `KNOWN_THEOREM_FORMALIZED_WITH_PROJECT_SPECIALIZED_PHASE_ARGUMENT`.

`hard_gap_before`: L2/G5 selected, reverse all-index positivity-to-RH implication open.

`hard_gap_after`: L2/G5 complete, exact project Li criterion Lean-equivalent to
`Mathlib.RiemannHypothesis`.

`hard_gap_delta=1`.

`assumption_frontier_before`: RH and all-index Li nonnegativity were equivalent only at the
literature level; the project had compiled only the RH-forward direction.

`assumption_frontier_after`: the equivalence is compiled with no new premise, but neither
equivalent side is proved unconditionally. The global RH goal remains active.

Next state after publication: `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Loop Closure

The implementation and evidence-backfill commits are public and independently pass Lean Action
CI. This campaign is closed as
`KNOWN_THEOREM_FORMALIZED_WITH_PROJECT_SPECIALIZED_PHASE_ARGUMENT`, `hard_gap_delta=1`.
L2/G5 is complete. This closes an exact criterion edge but does not prove RH or all-index Li
nonnegativity unconditionally. The persistent RH goal remains active, and route selection must now
move through independent audit rather than manufacture another local Li helper.
