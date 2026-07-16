# R5 Compact C6 Explicit Formula Campaign

Campaign: `CAMPAIGN-20260716-R5-COMPACT-C6-EXPLICIT-FORMULA-01`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_campaign`: yes

## Loop 1: interface audit and route selection

- Re-read the post-compaction HANDOFF, fixed W1/W2 frontier, strip-class interfaces, exact
  Baez-Duarte Gram modules, Burnol lower-bound closure, and the prior Wong, Carvill, and sparse-span
  stop records.
- Confirmed that the old sparse family has a valid lower frame bound but an exact Lean-checked
  orthogonal target witness, so improving its constants cannot advance target closure.
- Screened the new Pyvovarov arXiv `2607.12084v1`. Its exponentially damped approximants lie in
  the natural closure for each positive damping parameter, but the paper leaves norm continuity at
  zero as the decisive difficulty. That is not an unconditional successor edge.
- Screened five exact candidates in
  `research/r5_compact_c6_explicit_formula_prereg_20260716.md` and selected only C4.
- Fixed the complete compact `C^6` arithmetic explicit formula before mathematical source edits.
- `result`: `ROUTE_SELECTION_COMPLETE`
- `hard_gap_delta`: zero during selection
- `next_state`: `PROOF_ATTEMPT_A`

## Loop 2: finite-order Fourier inversion and exact endpoint

- Generalized the compact zero-cutoff estimates from `ContDiff R infinity` to
  `ContDiff R 6`, while preserving every old smooth theorem as a compatibility corollary.
- Proved finite-order transform identities through six derivatives and reused the resulting
  inverse-sixth decay for the selected xi top edge.
- Removed the arithmetic proof's Schwartz dependency. General Fourier inversion now follows from
  continuity and inverse-square Fourier decay; the first absolute Fourier moment follows from
  inverse-sixth decay.
- Lean proves the preregistered endpoint
  `symmetrizedCompactLaplaceXi_arithmetic_explicit_formula_sixContDiff` with the unchanged
  multiplicity-bearing zero sum, pole term, GammaR integral, and finite von-Mangoldt sum.
- Both edited analytic modules compile independently without diagnostics. Exact Targets and
  TargetChecks pass, `git diff --check` passes, forbidden declaration and proof-token scans are
  empty, and the full 8,681-job project build succeeds.
- Five selected transitive axiom prints contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Preregistration commit `540b0ddcbf90a219084f8fdcb80a02ddaad5e277` passed public Lean Action CI
  run `29467845311`, build job `87524663724`, in approximately `2m3s`.
- `result`: `LOCAL_ENDPOINT_COMPLETE`
- `classification`: `BRIDGE_REDUCED`
- `hard_gap_delta`: one only at the compact finite-regularity edge `W1c1c2`
- `unchanged_frontier`: quotient/completeness, full-class regularization, W2/G7, G3/M2, and RH
- `next_state`: `PUBLIC_IMPLEMENTATION_GATE`

## Loop 3: public implementation gate

- Implementation commit `3e3c677495c592096d7843aa4845e861bc393937` passed public Lean Action CI
  run `29468797210`, build job `87527584998`, in `2m0s`.
- The clean public checkout independently verifies the exact C6 endpoint, compatibility corollary,
  target checks, and transitive axiom audit.
- `result`: `PUBLIC_IMPLEMENTATION_VERIFIED`
- `classification`: `BRIDGE_REDUCED`
- `hard_gap_delta`: unchanged at one only for `W1c1c2`
- `next_state`: `IMMUTABLE_EVIDENCE_BACKFILL`
