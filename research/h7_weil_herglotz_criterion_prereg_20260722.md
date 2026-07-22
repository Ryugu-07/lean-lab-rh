# H7 Finite Herglotz Criterion Preregistration

Date: 2026-07-22

Campaign: `LITERATURE-20260722-H7-WEIL-HERGLOTZ-CRITERION-01`

Mode: `LITERATURE`

Status: `LOCAL_ENDPOINT_PROVED / PUBLIC_IMPLEMENTATION_CI_PENDING`

## Baseline and value-ranked route decision

- `parent_commit`: `c5ba3ab66e9a61446da7ad43d3a1d3786efd220d`.
- `baseline_public_ci`: Lean Action run `29930876406`, build job `88959943824`, passed in
  `1m45s`.
- `preregistration_commit`: `47d6adb4d8f25bf3d631cd449159a98eb1b94c20`.
- `preregistration_public_ci`: Lean Action run `29931671154`, build job `88962703883`, passed in
  `1m55s` before proof-source implementation began.
- `previous_campaign`: `LITERATURE-20260722-H7-WEIL-FINITE-MATRIX-PARITY-01` publicly compiled
  the exact finite divided-difference matrix and a strict two-block Rayleigh certificate. It did
  not prove either strict block inequality for an arithmetic Weil matrix.
- `selected_node`: `H7-WEIL-GROUNDSTATE-HERGLOTZ-01`.
- `route_comparison`: the true ground-state-to-`k_lambda` limit remains RH-strength but still
  depends on simple-even structure and unresolved form-domain alignment. H1 short-mollifier
  optimization remains the historical runner-up but does not presently repair this H7 edge. Four
  newly audited June 2026 sources reduce the H7 odd-sector comparison to one scalar rank-one
  resolvent inequality. Formalizing that exact reduction is therefore the highest-value bounded
  continuation of the selected historical door.
- `material_difference`: this campaign replaces the previous all-vector odd Rayleigh premise by
  a source-aligned pole-free positivity condition plus one scalar Herglotz inequality. It does not
  reprove parity splitting and does not assert that the arithmetic scalar inequality holds.
- `global_goal`: active; no finite rank-one criterion alone proves RH.

## Source boundary

The direct sources are four unreviewed June 2026 Zenodo preprints by Breno Wilson de Andrade
Silva, registered at S3:

- DOI `10.5281/zenodo.20682834`: pole-free Perron structure and rank-two pole splitting;
- DOI `10.5281/zenodo.20694588`: scalar Herglotz criterion for even-simplicity;
- DOI `10.5281/zenodo.20710075`: prime-block Loewner formula and parity sign law;
- DOI `10.5281/zenodo.20737111`: parity-sector Loewner identities and a bordered scalar criterion.

The rank-one positivity equivalence itself is standard finite-dimensional linear algebra. The S3
operator claims, numerical tables, pole-free Perron theorem, and uniform arithmetic inequality are
not project premises. This campaign proves only the exact finite algebra needed to state and test
the claimed reduction.

## Exact mathematical target

Let `P` be a real symmetric matrix on the centered band, let `S` and `u` be reflection-odd
vectors, and assume

```text
P*u = S,
q_P(y) > 0 for every nonzero odd y,
S != 0.
```

Write `m=S dot u` and `P_S=P-2*S*S^T`. Prove the exact completion-of-square identity

```text
q_(P_S)(y)
  = q_P(y-2*(S dot y)*u) + 2*(S dot y)^2*(1-2*m).
```

Then prove the source rank-one criterion

```text
(q_(P_S)(y)>0 for every nonzero odd y) <-> 2*m<1.
```

The forward implication must use the test vector `u`; the reverse implication must prove strict
positivity in both cases `y-2*(S dot y)*u != 0` and equality to zero. No determinant, floating-point
eigenvalue, or unproved inverse API may replace this proof.

Finally define a finite Herglotz certificate for an original reflection-commuting symmetric matrix
`A`, candidate even eigenpair `(mu,xi)`, pole-free shifted odd form `P`, pole vector `S`, and
resolvent vector `u`. Its assumptions are:

1. `xi` is even, normalized, and satisfies `A*xi=mu*xi`;
2. the strict even-complement Rayleigh condition from the previous campaign;
3. `P` is symmetric and strictly positive on nonzero odd vectors;
4. `S,u` are odd, `S!=0`, and `P*u=S`;
5. on odd vectors, the Rayleigh defect of `A` at `mu` equals the quadratic form of
   `P-2*S*S^T`;
6. the scalar condition `2*(S dot u)<1`.

Prove that this certificate constructs `WeilFiniteParityRayleighCertificate` and hence
`WeilFiniteEvenSimpleGroundState` through the already audited endpoint.

## Proposed Lean spine

The intended production module is `LeanLab/Riemann/WeilGroundStateHerglotz.lean`. Final statement
syntax may change only to match checked Mathlib APIs without weakening the mathematics. Proposed
declarations:

1. `weilFiniteRankOneDeflation`;
2. `weilFiniteRankOneDeflectionQuadratic` for the completion-of-square identity;
3. `weilFiniteOddRankOneStrict_iff_resolvent` for the exact scalar iff;
4. `WeilFiniteOddHerglotzCertificate`;
5. `WeilFiniteOddHerglotzCertificate.parityRayleighCertificate`;
6. `WeilFiniteOddHerglotzCertificate.evenSimpleGroundState`.

The exact identity, both directions of the iff, the certificate consumer, and final simple-even
endpoint receive TargetChecks. Selected declarations receive `#print axioms` entries.

## Success, falsification, and stopping criteria

- `success`: Lean proves the completion-of-square identity, exact strict-positivity iff, and the
  consumer into the previous simple-even endpoint; all mechanical gates and public CI pass.
- `meaningful_partial`: the identity compiles but one direction is reduced to a precisely named
  finite-dimensional strictness or parity obstruction not already assumed.
- `falsification`: the source sign `P-2*S*S^T`, scalar threshold `1/2`, or stated hypotheses do not
  imply the advertised finite iff. Record the exact counterexample or missing hypothesis and do
  not use the source criterion.
- `no_progress`: Mathlib expression issues remain after the algebraic identity is represented
  exactly. Record the API boundary and route-select; do not manufacture unrelated matrix lemmas.
- `local_stop`: stop after the finite iff and certificate consumer are publicly closed, or after a
  kernel-checked falsification. The actual arithmetic inequality and all infinite-operator claims
  are separate campaigns.

## Assumption and implication audit

- `assumption_frontier_before`: simple-even requires strict positivity on every nonzero odd vector.
- `assumption_frontier_after_on_success`: under source pole localization, odd positivity is
  equivalent to the single scalar resolvent bound. The bound itself remains unproved.
- `rh_strength`: neither the generic iff nor one fixed finite certificate implies RH. A uniform
  arithmetic theorem is still needed, and the true ground-state limit remains separately open.
- `not_a_conjecture_premise`: the S3 scalar inequality is an open target, never a field supplied to
  downstream theorems except explicitly as a hypothesis.
- `expected_deltas`: `rh_frontier_delta=0`, `hard_gap_delta=0`,
  `route_infrastructure_delta=1`, `obstruction_map_delta=1`.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: one inherited recovery occurred during implementation; the canonical
  governance, frontier, current campaign files, complete source, external ACTIVE ledger, and git
  status were re-read before proof work resumed.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit only this preregistration and synchronized research ledgers first. Public Lean Action CI
must pass before `WeilGroundStateHerglotz.lean`, Targets, TargetChecks, AxiomsAudit, or aggregate
imports are edited.

## Local outcome

- `result`: `PROVED / KNOWN_FINITE_LINEAR_ALGEBRA_FORMALIZED /
  SOURCE_ASSUMPTION_WEAKENED / FINITE_CERTIFICATE_CONSUMER`.
- `compiled_identity`: `weilFiniteRankOneDeflectionQuadratic` proves the registered completion of
  squares exactly for the source sign and coefficient `2`.
- `compiled_iff`: `weilFiniteOddRankOneStrict_iff_resolvent` proves both directions of the strict
  odd-sector rank-one criterion, using `u` in the forward direction and the registered zero/nonzero
  split for `y-2*(S dot y)*u` in the reverse direction.
- `assumption_weakening`: the generic iff does not require `S` to be reflection-odd. The proof only
  needs `u` odd in order to keep the shifted test vector odd. The source-aligned certificate retains
  `odd_S`; this weakening does not prove the arithmetic scalar inequality.
- `compiled_consumer`: `WeilFiniteOddHerglotzCertificate.parityRayleighCertificate` constructs the
  previous finite parity certificate, and `.evenSimpleGroundState` reaches the registered
  simple-even endpoint under the original matrix symmetry/reflection assumptions.
- `mechanical_gate`: the 171-line production module, Targets, six exact TargetChecks, and six
  selected axiom prints compile. The selected declarations depend only on `propext`,
  `Classical.choice`, and `Quot.sound`; the production-module forbidden scan and
  `git diff --check` are empty; the full build passes with 8,739 jobs.
- `classification_boundary`: no arithmetic `2*(S dot u)<1` theorem, uniform spectral gap,
  ground-state-to-`k_lambda` comparison, or RH theorem is claimed.
- `deltas`: `rh_frontier_delta=0`, `hard_gap_delta=0`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=1`, `source_assumption_weakening_delta=1`.
- `next_gate`: publish the implementation commit and require public Lean Action CI before any
  evidence backfill or route selection.
