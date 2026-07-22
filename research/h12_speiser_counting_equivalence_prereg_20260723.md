# H12 Speiser Counting-Equivalence Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H12-SPEISER-COUNTING-EQUIVALENCE-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Baseline and route selection

- `parent_commit`: `418a1b3e469a0a71e67ba39ac22eb0dd974d37f3`.
- `parent_public_ci`: Lean Action run `29940746044`, build job `88993661951`, passed in `1m30s`.
- `previous_campaign`: H9 Conrey rationality-gap is publicly closed. It isolates the actual
  flat-prefix obligation, but further generic affine algebra or a larger finite scan would not
  attack that arithmetic obligation.
- `selected_node`: `H12-SPEISER-LEVINSON-MONTGOMERY-COUNT-01` inside ranked door D10.
- `route_comparison`: H11 pair correlation has no real-part information; H10 still lacks a
  number-field trace/cohomology object; H2 density and H1 proportions both lack a mechanism that
  excludes one finite or sparse off-line orbit. Speiser supplies exactly such a localizer by
  replacing off-line zeta zeros with left-half-strip zeros of `zeta'`.
- `material_difference`: this campaign reconstructs the rigorous zero-count proof of a historical
  theorem and exposes its exact analytic hinge. It does not merely add another textual equivalent
  criterion, and it does not use Speiser's informal level-curve picture as a premise.
- `global_goal`: active; Speiser's theorem is an RH equivalence, not an unconditional RH proof.

## Primary sources and bibliographic correction

1. Andreas Speiser, *Geometrisches zur Riemannschen Zetafunktion*, Mathematische Annalen 110
   (1935), 514-521. The result is often called Speiser's 1934 theorem, but the EuDML volume record
   is 1935.
2. Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the Riemann zeta-function*,
   Acta Mathematica 133 (1974), 49-65.

The 2003 expository reconstruction by J. Arias-de-Reyna reports that the original geometric proof
needs gaps filled and points to Levinson-Montgomery for a rigorous stronger theorem. It is used
only to identify why the geometric argument is not a formal premise.

## Source audit and exact hinge

For `s=sigma+i*t`, Levinson-Montgomery let `N_-(T)` count zeros of `zeta` and `N'_-(T)` count
zeros of `zeta'` in

```text
0 < t < T, 0 < sigma < 1/2,
```

with multiplicity. Their Theorem 1 proves

```text
N'_-(T) = N_-(T) + O(log T).
```

More decisively, unless `N_-(T)>T/2` for every sufficiently large `T`, it produces an unbounded
sequence `T_j` for which

```text
N'_-(T_j) = N_-(T_j)
```

exactly. The corollary is Speiser's equivalence. The asymptotic `O(log T)` relation alone permits
finitely many exceptions and is insufficient; the exact equality subsequence is the logical
localizer.

The proof of that equality uses the real part of `zeta'/zeta` on an indented rectangle: a
functional-equation zero sum, Gamma estimates, a low-height boundary verification, indentation
around critical-line zeros, and an argument-principle count. If no suitable top boundaries exist,
the same zero sum forces at least linearly many left-half zeta zeros. These are mathematical proof
obligations, not assumptions licensed by this preregistration.

## Exact mathematical target

Define the source-aligned upper-left Speiser condition

```text
SpeiserDerivativeZeroFree :=
  for every s, 0 < Im(s), 0 < Re(s), and Re(s) < 1/2 imply zeta'(s) != 0.
```

The full target is

```text
Mathlib.RiemannHypothesis iff SpeiserDerivativeZeroFree.
```

Multiplicity and boundary conventions must match the source: the count uses the open upper-left
half of the critical strip, excludes the pole and trivial real derivative zeros, and treats zeros
on the critical line by indented contours rather than counting them on either side.

## Proposed Lean spine

The intended module is `LeanLab/Riemann/SpeiserCountingEquivalence.lean`.

1. `speiserUpperLeftStrip` and `SpeiserDerivativeZeroFree`;
2. analyticity of `deriv riemannZeta` on that strip;
3. a locally finite multiplicity-bearing divisor for `deriv riemannZeta` on the strip;
4. exact support/zero and compact-rectangle finiteness theorems;
5. multiplicity-bearing left zeta and zeta-derivative rectangle counts;
6. an exact count consumer: an unbounded sequence of equal counts plus derivative zero-freeness
   excludes every upper-left zeta zero;
7. reflection from any RH counterexample to an upper-left zeta zero;
8. the full `riemannHypothesis_iff_speiserDerivativeZeroFree` theorem after the source boundary
   argument is compiled.

Partial declarations are classified as route infrastructure only. The campaign succeeds only if
the full equivalence compiles, or stops with the first exact unproved analytic source obligation
recorded without promoting it to a premise.

## Success, falsification, and stopping criteria

- `success`: the exact equivalence, TargetChecks, definition alignment, and selected axiom audit
  compile and pass public CI.
- `meaningful_partial`: the derivative divisor and exact-count consumer compile, while the
  Levinson-Montgomery boundary theorem is reduced to a named source-faithful analytic statement.
  This has `rh_frontier_delta=0` and does not count as full campaign success.
- `falsification`: an exact definition mismatch, unhandled boundary zero, or failed multiplicity
  correspondence invalidates the proposed statement and triggers correction before proceeding.
- `no_progress`: if the first missing source step requires unavailable Jensen/Littlewood or
  meromorphic argument-principle infrastructure, record its complete Lean statement and API
  inventory; never assume it.
- `local_stop`: full equivalence is public-green, or the reconstruction reaches one precise
  external analytic obstruction with no honest smaller theorem that advances the source chain.

## Known obstacles

- The project has an exact xi divisor but no divisor or count interface for `deriv riemannZeta`.
- Mathlib supplies analyticity of zeta away from `1` and analytic derivatives, but no specialized
  Levinson-Montgomery zero-count theorem.
- The source proof uses an indented rectangle whose boundary changes around critical-line zeros.
- The low-height sign verification and large-height Gamma/zero-sum estimates must be theorem-level
  inputs, not numerical prose.
- An asymptotic difference bound cannot replace the exact equality subsequence.

## Assumption and implication audit

- `assumption_frontier_before`: H1/H2 can make off-line zeros sparse but cannot exclude the last
  one; the project has no compiled `zeta'` left-strip localizer.
- `assumption_frontier_after_on_success`: Speiser's exact known equivalence is available with all
  source conventions and no new nonstandard axioms. The unconditional side remains precisely
  `SpeiserDerivativeZeroFree`.
- `rh_strength`: the final condition is equivalent to RH. It cannot be used as a weaker premise.
- `cross_route_value`: any future H1/H2 theorem forcing the natural-valued left derivative count
  below one on an unbounded sequence would close the last-exception gap through the compiled
  count consumer, but such an estimate is not currently known or assumed.
- `expected_deltas`: `rh_frontier_delta=0`; `route_infrastructure_delta=1` on a meaningful partial;
  `known_equivalence_formalization_delta=1` only on full success.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: one inherited-summary recovery occurred during the preceding H9 campaign;
  canonical files were re-read before this selection.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit only this preregistration, its attempt log, H9 final-CI backfill, source-registry correction,
and synchronized route ledgers. Public Lean Action CI must pass before editing any H12 Lean proof
source, Targets, TargetChecks, AxiomsAudit, or aggregate imports.

## Implementation result

- `preregistration_commit`: `178d86eaa7d02d8eb88421171bee8964c722fb0e`.
- `preregistration_public_ci`: Lean Action run `29941747166`, build job `88997067033`, passed in
  `1m33s`.
- `result`: `MEANINGFUL_PARTIAL / FINAL_LEDGER_CI_REQUIRED`.
- The 465-line production module constructs the actual derivative divisor and both finite
  multiplicity-bearing counts. It proves the exact count consumer, the real-axis base fact by
  cross-route H6 positivity, and the full conditional equivalence from the two source-faithful
  Levinson-Montgomery Theorem 1 outputs.
- Source logic was corrected during implementation: exact equality is not unconditional. The Lean
  interface separately records the `O(log T)` bound and exact-or-linear-density dichotomy, proves
  the former is sublinear, and uses both to force the exact branch under either zero-free condition.
- `local_stop`: reached. The first exact external analytic obstruction is the conjunction of
  `LevinsonMontgomeryLogCountBound` and `LevinsonMontgomeryCountDichotomy` for the actual counts.
  The full Speiser equivalence is not claimed.
- Five exact TargetChecks and five selected standard-only axiom prints pass. Full `lake build`
  passes 8,742 jobs. Implementation commit `2a6290a27fd7675db409f884679d1a554c13b72d`
  passed public Lean Action run `29943873685`, build job `89004249306`, in `2m6s`; Lean proof
  source is frozen. Evidence commit `eeca9f7fc910b323df7aaaec00f3258c92063483` passed run
  `29944285692`, build job `89005620974`, in `1m33s`. Final-ledger CI is the remaining local gate;
  H12-D/H12-E and RH remain open after this campaign stops.
