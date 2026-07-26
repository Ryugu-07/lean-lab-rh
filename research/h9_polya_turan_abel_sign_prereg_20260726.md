# H9 Pólya--Turán Abel Sign Audit Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-POLYA-TURAN-ABEL-SIGN-AUDIT-01`

Selected node: `H9-POLYA-TURAN-ABEL-SIGN-AUDIT-01`

Mode: `LITERATURE / FORMALIZATION / FALSIFICATION`

Status: `LOCAL_FULL_ABEL_AUDIT_SUCCESS / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Baseline and selection

- `parent_commit`: `e36b2494284982ec276dc1f04cb86313f68eeb28`.
- `parent_public_ci`: Lean Action run `30184071394`, build job `89745543598`, passed in
  `1m34s`.
- `previous_campaign`: the H1 inverse-Mellin support, boundedness, convolution, and source
  integral bound are publicly closed.  Its Cauchy--Schwarz/moment transfer remains open, but
  another immediate H1 campaign is not automatic.
- `selected_node`: H9 arithmetic criteria and the D13 failed-mechanism control card.
- `selection_reason`: the historical atlas names Pólya-type failures but supplies no exact
  Pólya--Turán card and no Lean attempt.  This is a coverage defect under the user's
  omission-seeking historical policy.
- `global_goal`: active.  RH is the target; this campaign audits one historical route and does not
  replace it.

## Locked sources and route separation

1. George Pólya, *Verschiedene Bemerkungen zur Zahlentheorie* (1919), introduces the unweighted
   Liouville summatory sign problem.
2. A. E. Ingham, *On Two Conjectures in the Theory of Numbers* (1942), derives strong zeta-zero
   consequences from the Pólya sign premise and supplies the oscillatory framework later used to
   disprove it.
3. Paul Turán, *On Some Approximative Dirichlet-polynomials in the Theory of the Zeta-function of
   Riemann* (1948), treats both harmonic-weighted Liouville sums and finite zeta Dirichlet
   polynomials.  These are distinct mechanisms.
4. C. B. Haselgrove, *A Disproof of a Conjecture of Pólya* (1958), proves the Pólya sign premise
   false.
5. Peter Borwein, Ron Ferguson, and Michael Mossinghoff, *Sign changes in sums of the Liouville
   function* (2008), certifies the first negative harmonic-weighted Turán sum and studies both
   historical sums.
6. Emre Alkan, *Variations on criteria of Pólya and Turán for the Riemann hypothesis* (2021),
   supplies modern all-parameter repaired equivalences.  These are recorded as equivalences, not
   unconditional progress.
7. Robert Spira, *Zeros of Sections of the Zeta Function* (1968), supplies explicit finite-section
   zeros outside Turán's proposed zero-free half-plane.
8. Hugh L. Montgomery, *Zeros of Approximations to the Zeta Function* (1983), proves a
   sufficiently-large-section zero result that closes the asymptotic finite-section shortcut.

The project must not merge:

- `L(N) = sum_(n<=N) lambda(n)`;
- `T(N) = sum_(n<=N) lambda(n)/n`;
- zeros of `sum_(n<=N) n^(-s)`;
- later all-parameter weighted/derivative criteria.

## Exact mathematical endpoint

For an arbitrary rational sequence `a`, define

```text
A_a(N) = sum_(1<=n<=N) a(n)
W_a(N) = sum_(1<=n<=N) a(n)/n.
```

Prove for every `N >= 1` the exact finite Abel identity

```text
W_a(N)
  = A_a(N)/N
    + sum_(1<=k<N) A_a(k) * (1/k - 1/(k+1)).
```

Instantiate it with Mathlib's exact integer-valued `ArithmeticFunction.liouville`, cast to
`Rat`.  Isolate `A_lambda(1)=1` and the positive Abel coefficients.  Prove the strongest
source-relevant finite sign consequence:

```text
(forall 2<=k<=N, A_lambda(k)<=0) -> T(N)<=1/2.
```

The campaign must not infer `0<=T(N)` from this premise.  It must additionally compile a finite
exact rational sequence with first term `1`, all later prefix sums nonpositive on its registered
range, and a negative harmonic-weighted sum.  This witness falsifies only the generic sign-logic
shortcut; it is not a Liouville counterexample and says nothing new about the published large
counterexample.

## Proposed Lean spine

Create `LeanLab/Riemann/PolyaTuranAbelAudit.lean` only after public preregistration CI.

1. `finitePrefixSum` and `finiteHarmonicWeightedSum` over exact rational arithmetic;
2. recurrence theorems at `N+1`;
3. `finiteHarmonicWeightedSum_eq_abel`;
4. `polyaLiouvilleSum` and `turanLiouvilleSum`;
5. exact source-alignment checks at `N=1`;
6. `turanLiouvilleSum_eq_abel`;
7. the finite Pólya-prefix upper bound `T(N)<=1/2`;
8. the generic finite negative-weighted witness;
9. aggregate `polyaTuranAbelSignAudit_endpoint`.

Names may change to fit Mathlib's APIs.  The endpoint may not replace exact `Rat` sums by floating
point computation, and may not use the historical false sign claims as hypotheses outside their
explicit finite conditional theorem.

## Success, falsification, and stop conditions

- `FULL_ABEL_AUDIT_SUCCESS`: the exact generic Abel identity, Liouville specialization, finite
  sign consequence, generic witness, aggregate theorem, Targets, TargetChecks, axiom audit,
  forbidden scans, full build, and public evidence sequence all pass.
- `SOURCE_MISMATCH`: a source uses a different Liouville convention, weighting, endpoint, or sign.
  Correct the card and definitions before proving anything.
- `SIGN_SHORTCUT_SURVIVES`: the registered generic witness is impossible because the finite Abel
  identity plus the stated prefix premise actually forces weighted nonnegativity.  Prove that
  theorem instead and record the contradiction with the proposed witness.
- `API_BLOCKED`: record the first exact missing finite-sum theorem if rational division or
  interval indexing cannot be handled without weakening the source statement.
- `local_stop`: full public closure, source mismatch, or one exact blocked theorem with no honest
  smaller source advance.  A local stop returns to `ROUTE_SELECTION`; the global RH Goal remains
  active.

## RH-strength and originality audit

- The two historical global sign premises are stronger than ordinary finite checks and are known
  false.  They are never admitted as project assumptions.
- The finite Abel identity is classical known mathematics and is not claimed novel.
- The generic witness is a logic audit, not an arithmetic assertion about Liouville.
- Alkan's repaired criteria are RH equivalences.  They remain unavailable as premises unless
  their sign conditions are proved.
- `expected_deltas`: `rh_frontier_delta=0`,
  `historical_route_coverage_delta=1`, `sign_logic_obstruction_delta=1`.

## Known obstacles

- Mathlib's `ArithmeticFunction.liouville` is integer-valued; all casts into `Rat` must be explicit.
- The source sums begin at one, while `Finset.range` begins at zero.
- Denominators must carry nonzero witnesses rather than being simplified informally.
- The initial prefix `A_lambda(1)=1` prevents a careless claim that Pólya's `N>=2`
  nonpositivity would make every Abel term nonpositive.
- Large published counterexample indices are external computational results and are outside this
  fixed endpoint.
- Spira's and Montgomery's finite-section zero theorems remain source-recorded obstructions; this
  campaign does not replace them with floating-point roots or an unproved zero certificate.

## Mechanical and publication gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation.  Require exact TargetChecks, selected transitive `#print axioms`, empty forbidden
scans, `git diff --check`, direct module compilation, full `lake build`, frozen implementation
CI, immutable-evidence CI, and final-ledger CI.

Commit only documentation and ledgers first.  Public Lean Action CI must pass before creating or
editing the production Lean module, Targets, TargetChecks, AxiomsAudit, or aggregate imports.  The
six inherited user/exposure files remain untouched and unstaged.

## Execution result

- The preregistration gate passed at commit
  `f6f1329558bca0aa233bbaa472604c2bacbd6fa4`, Lean Action run `30184412364`, build job
  `89746411347`, in `2m2s`.
- The production module proves the exact generic Abel identity and its Liouville specialization.
- The strongest registered finite sign consequence is
  `turanLiouvilleSum (N+2) <= 1/2` under Pólya-prefix nonpositivity from index two.
- The registered generic witness is stronger than the bounded proposal: every prefix from index
  two onward equals `-2`, while the second harmonic-weighted sum is `-1/2`.
- Aggregate theorem `polyaTuranAbelSignAudit_endpoint`, the proven Target, exact TargetChecks,
  and six selected axiom prints compile.
- The 244-line source is warning-free. Forbidden scans and `git diff --check` are empty; the full
  build passes `8761/8761`.
- This is `FULL_ABEL_AUDIT_SUCCESS` locally with
  `historical_route_coverage_delta=1`, `sign_logic_obstruction_delta=1`, and
  `rh_frontier_delta=0`. Public implementation and immutable-evidence gates remain.
