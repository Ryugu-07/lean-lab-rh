# R5 Compact Weil Criterion Campaign

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-CRITERION-01`

Status: `PUBLICLY_CLOSED`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_campaign`: no

## Loop 1: independent route map

- Rotated from the previous FALSIFICATION campaign to LITERATURE.
- Re-audited W1/W2, the parked Baez-Duarte/Burnol routes, the raw Lagarias strip class, the compact
  C6 formula, and the complete-divisor compact separator.
- Confirmed that Wong, Carvill, the sparse Gram family, Pyvovarov zero-damping continuity, and
  unconditional compact positivity remain closed or parked at their recorded frontiers.
- `result`: `ROUTE_MAP_COMPLETE`
- `hard_gap_delta`: zero during audit

## Loop 2: five-candidate source screen

- Compared the exact compact criterion, Delsarte rapid-strip extension, raw strip completion,
  Arias de Reyna temperedness, and the Connes--Consani semi-local operator route.
- Only Appendix C Proposition C.1 has a complete adjacent mechanism using newly public project
  prerequisites. The other four candidates either require a larger distribution/operator theory or
  hide an RH-equivalent premise.
- `result`: `ONE_CANDIDATE_SURVIVES`
- `hard_gap_delta`: zero during selection

## Loop 3: adversarial admission

- Fixed arbitrary finite `F`, both endpoint moments, the additive-log conjugate involution, exact
  sign convention, equal-value multiplicity behavior, and a reverse witness at the pair
  `rho, 1-conj(rho)`.
- Avoided assuming a conjugation permutation of divisor indices: the planned tail proof uses an
  absolute `ell^1` first factor and a uniform closed-strip bound for the partner.
- The old anti-cycling rejection is not silently overturned. New evidence consists of the public
  compact C6 arithmetic formula and public complete-divisor separator; the selected endpoint is the
  full arbitrary-`F` source proposition, not another fixed Gaussian criterion.
- `result`: `PREREGISTERED`
- `classification_if_successful`: `KNOWN_THEOREM_FORMALIZED` or `BRIDGE_REDUCED`
- `hard_gap_delta_if_successful`: one at the W1/G6 compact criterion edge; zero for W2/G7 and RH
- `next_state`: `PUBLIC_PREREGISTRATION_GATE -> PROOF_ATTEMPT_A`

## Loop 4: public preregistration and forward implication

- Public preregistration commit `55a634402aa0dc5db4266ee56c499efb7d6c5d13` passed Lean Action CI run
  `29484731600`, build job `87576390864`, in `1m35s` before proof-source edits began.
- Added the additive-log conjugate involution and proved exact Laplace covariance
  `G*(s) = conj(G(1-conj(s)))`, with smoothness and compact-support preservation.
- Proved xi conjugation reality and closure of nontrivial zeros under conjugation and conjugate
  reflection without assuming a divisor-index conjugation permutation.
- Defined the compact autocorrelation, the complete divisor zero quadratic, and the exact
  finite-prime/GammaR arithmetic quadratic. With `G(0)=G(1)=0`, the public compact explicit
  formula gives `arithmeticQuadratic = pi * zeroQuadratic` exactly.
- Under RH, every autocorrelation value at a divisor zero is a norm square. Reflection handles the
  second symmetrized value, complete summability justifies `re_tsum`, and the exact arbitrary-`F`
  forward implication now compiles.
- `result`: `FORWARD_DIRECTION_COMPILES`
- `hard_gap_delta`: zero until the preregistered iff, especially its reverse direction, compiles
- `next_state`: `PROOF_ATTEMPT_A_CONSTRAINED_SEPARATOR`

## Loop 5: constrained separator and complete reverse implication

- Strengthened the compact complete-divisor separator to vanish exactly on an arbitrary finite
  set disjoint from the protected target while preserving normalization, absolute summability,
  and an arbitrarily small strict `ell^1` tail over all different zero values.
- For an off-line divisor value `rho`, set `sigma = 1-conj(rho)`, constructed separators at both
  targets, and subtracted them. The resulting transform is `1` at `rho`, `-1` at `sigma`, and zero
  on the source-admissible finite set `F`.
- The reverse tail proof uses no conjugation permutation. For every non-target zero `z`, the value
  `1-conj(z)` is a nontrivial zero and therefore has some divisor index. The same strict tail then
  bounds the partner factor pointwise. One selected term is `-1`, equal-value multiplicity copies
  are also `-1`, and all remaining terms have total upper bound below `1/16`.
- Proved that divisor reflection identifies the symmetrized zero quadratic with the raw
  autocorrelation `tsum`; endpoint vanishing removes the pole term, and positivity of `pi`
  transfers the off-line negative witness to the exact arithmetic quadratic.
- The fixed endpoint
  `riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg` now compiles with arbitrary
  finite zero-free `F` containing `0,1` and exact transform vanishing on `F`.
- Exact module, Target, and TargetCheck compilation pass. Six selected transitive axiom prints use
  only `propext`, `Classical.choice`, and `Quot.sound`; new-module and repository forbidden scans
  are empty; `git diff --check` passes; the full default build succeeds with 8,682 jobs.
- `result`: `LOCAL_ENDPOINT_VERIFIED`
- `classification_if_public_ci_passes`: `KNOWN_THEOREM_FORMALIZED`
- `hard_gap_delta_if_public_ci_passes`: one source-level W1/G6 compact-criterion edge; zero for
  W2/G7 and RH
- `next_state`: `PUBLIC_IMPLEMENTATION_GATE`

## Loop 6: public implementation verification

- Implementation commit `d590ee42e37366388800bafda04020a84eee8452` passed Lean Action CI run
  `29487332091`, build job `87584836879`, in `1m53s`.
- The independent public build includes the fixed iff endpoint, constrained separator, complete
  off-line negative witness, Targets, TargetChecks, and transitive axiom audit.
- `result`: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`
- `hard_gap_delta`: one W1/G6 compact-criterion edge, pending immutable evidence-backfill CI
- `next_state`: `PUBLIC_EVIDENCE_GATE`

## Loop 7: public evidence and campaign closure

- Evidence-backfill commit `03e1661b077ab8d3e2f8c9b93b19aa63c3c1eebc` passed Lean Action CI run
  `29487596817`, build job `87585683179`, in `2m6s`.
- Together with preregistration run `29484731600` and implementation run `29487332091`, the fixed
  endpoint has independent public preregistration, implementation, and immutable evidence builds.
- `result`: `KNOWN_THEOREM_FORMALIZED`
- `hard_gap_delta`: one source-level W1/G6 compact-criterion edge; zero for W2/G7 and RH
- `remaining_open`: quotient/completeness and full-class regularization in W1/G6; unconditional
  positivity W2/G7; G3/M2; RH
- `next_state`: `PUBLIC_CLOSURE_COMMIT -> INDEPENDENT_AUDIT -> ROUTE_SELECTION`
