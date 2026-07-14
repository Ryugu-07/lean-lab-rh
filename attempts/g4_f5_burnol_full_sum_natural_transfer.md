# G4-F5 Burnol Full Sum And Natural Transfer

Date: 2026-07-14

- `batch_id`: `BATCH-20260714-G4-F5`
- `node_id`: `B1`
- `gap_id`: `G4/F5`
- `work_class`: `SOURCE_FORMALIZATION`
- `status`: active
- `hard_gap_before`: F0-F4 complete; F5 selected; M2/G3 parked and unchanged.
- `assumption_frontier_before`: the full finite-supremum passage and natural subsequence transfer
  are not yet in the checked theorem graph.

## Source Audit

The pinned Burnol v2 source at lines 649-670 states the full-zero lower bound and proves the
finite-set estimate now supplied by F4. Passing from all finite sets to the full nonnegative sum
is the remaining source step. F0 independently supplies the project natural-subspace consequence
through `V_N <= B_(1/N)`, `D(1/N) <= d_N`, and `1/N -> 0+`.

## Selected Route

Represent the full constant in `ENNReal`, where arbitrary nonnegative sums and value `top` are
native. Use `ENNReal.tsum_eq_iSup_sum` and `ENNReal.orderIsoRpow` to reduce the full continuous
bound exactly to F4. Then use `Tendsto.liminf_le_liminf_comp` with the reciprocal-natural map,
prove the eventual F0 pointwise comparison after the exact logarithmic normalization, and apply
liminf monotonicity.

## Attempt Log

### Loop 1: source and interface audit

- Result: preregistered; implementation not started.
- Useful finding: the correct full constant is an extended `ENNReal` half-power, so no global
  summability assumption is needed.
- Useful finding: Mathlib directly provides both `ENNReal.tsum_eq_iSup_sum` and the positive-rpow
  order isomorphism needed to commute the half-power with the finite-sum supremum.
- Useful finding: `Tendsto.liminf_le_liminf_comp` has the required direction: the continuous
  liminf is at most the reciprocal-natural subsequence liminf.
- Scope correction: F0 yields an asymptotic natural liminf bound, not the exact limiting-constant
  pointwise inequality for every `N`; the latter is excluded from the fixed endpoint.
- Next obstruction: compile the finite real/`ENNReal` conversion and the full iSup proof before
  editing the natural transfer.
- Classification: `FORMALIZATION_ONLY`; F5 and G4 remain open.

### Loop 2: full extended zero sum

- Result: internal Lean checkpoint complete; F5 remains active.
- `burnolZeroContribution` records the exact real term and Lean proves it nonnegative without a
  denominator-nonzero premise because both numerator and denominator are squares.
- `burnolFiniteZeroLowerConstant_eq_rpow` converts each F4 real square-root constant into the
  half-power of its finite `ENNReal` sum using nonnegativity, `ofReal_rpow`, and `ofReal_sum`.
- `ENNReal.tsum_eq_iSup_sum` expresses the arbitrary full sum as the supremum of finite subsums.
  The positive half-power order isomorphism commutes with that supremum, and every resulting
  finite term is bounded by the F4 endpoint.
- `RiemannHypothesis.burnolDistance_liminf_ge_fullZeroSum` now compiles with no summability,
  countability, or finiteness premise on the full sum.
- Verification: `lake env lean LeanLab/Riemann/BurnolFullLowerBound.lean` passes without warnings
  or proof placeholders.
- Next obstruction: transfer the continuous liminf along `N -> 1/N`, prove the exact
  `burnolLogScale (1/N) = log N` normalization, and compare with the natural distance.
- Classification: `FORMALIZATION_ONLY`; the natural endpoint and F5 closure remain open.

### Loop 3: reciprocal-natural liminf transfer

- Result: both exact F5 endpoints compile; repository gates remain pending.
- `burnolLogScale_inv_natCast` checks the exact normalization
  `burnolLogScale ((N : Real)⁻¹) = log (N : Real)`, including harmless totalized behavior at
  `N=0`.
- Eventually `N` is positive, so F0 supplies `D(1/N) <= d_N`. Monotonicity of `ENNReal.ofReal`
  and multiplication by the common square-root factor gives the scaled pointwise comparison.
- `tendsto_natCast_inv_nhdsWithin_Ioi_zero.liminf_le_liminf_comp` verifies that the continuous
  right-neighborhood liminf is bounded above by the reciprocal-natural subsequence liminf. A
  second liminf monotonicity step applies the F0 distance comparison.
- `RiemannHypothesis.baezDuarteNaturalDistance_liminf_ge_fullZeroSum` now proves the exact
  preregistered natural endpoint.
- An initial generic `liminf_le_liminf` application left its conditional-lattice boundedness
  auto-parameters unsolved. Supplying Mathlib's checked default lower/upper bounds explicitly
  resolved the interface issue without adding a mathematical premise.
- Verification: `lake env lean LeanLab/Riemann/BurnolFullLowerBound.lean` passes without warnings
  or proof placeholders.
- Next obstruction: integrate exact target witnesses and transitive axiom checks, run the full
  build and scans, then publish before closing F5 or G4.
- Classification: `KNOWN_THEOREM_FORMALIZED` provisionally; F5 remains active pending all gates.

### Loop 4: exact integration and local repository gates

- Result: every local F5 gate passes; public publication remains pending.
- `TargetChecks.lean` witnesses both preregistered theorem types exactly, including the full
  extended zero sum and the normalized natural-distance liminf.
- `AxiomsAudit.lean` reports only `propext`, `Classical.choice`, and `Quot.sound` for each final
  endpoint; no source theorem or transfer premise has been postulated.
- Full `lake build` passes with 8615 jobs. `git diff --check` passes, and scans find no
  `sorry`/`admit`/`sorryAx`, project `axiom`/`constant`/`opaque`, `native_decide`, or resource-limit
  relaxation in the new module.
- Hard-gap accounting: the checked theorem graph now contains the whole F5 edge locally, but F5
  and G4 remain selected/in progress until the implementation commit passes public Lean Action.
- Next obstruction: publish the implementation commit, require public CI success, then backfill
  immutable commit/run identifiers and close G4/B1.
- Classification: `KNOWN_THEOREM_FORMALIZED` provisionally; local verification complete.
