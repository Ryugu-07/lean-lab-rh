# RH exposure and bounded novelty audit (2026-07-16)

## Purpose and claim boundary

This document records the external-review surface and a reproducible, bounded search for prior
formalizations of the repository's principal RH criterion spines. It is not a proof of novelty and
does not support a "first formalization" claim. Negative search results below mean only that no
exact match was found in the named sources with the named queries as of 2026-07-16.

The project has not proved or disproved RH. The audited conclusions are equivalences with
mathlib's `RiemannHypothesis`, plus supporting analytic and algebraic lemmas.

## Formal surface exposed for review

| Surface | Top-level theorem | Mathematical source family |
| --- | --- | --- |
| Strong positive-natural closure | `riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure` | Baez-Duarte's strengthened Nyman-Beurling criterion |
| Li coefficients | `riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg` | Li (1997), with the zero-multiset reverse mechanism of Bombieri-Lagarias (1999) |
| Li-Weil finite Gram form | `riemannHypothesis_iff_forall_liWeilQuadratic_nonneg` | Bombieri-Lagarias' relation between Li positivity and Weil positivity |
| Compact arithmetic Weil form | `riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg` | Connes-Consani Appendix C, Proposition C.1, attributed there to Yoshida |

The compact theorem is quantified over a finite `F : Finset ℂ` disjoint from the nontrivial zeros
and containing `0,1`. Its test functions are smooth and compactly supported on the additive log
line, with compact Laplace transform vanishing on `F`. The arithmetic quadratic uses the project's
sign convention, so its displayed inequality is nonnegative while Connes-Consani display the
corresponding local Weil functional with the opposite sign.

## Search protocol and observations

### mathlib

- Fixed source: `leanprover-community/mathlib4`, tag `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Local source search terms: `Li coefficient`, `Li criterion`, `Baez-Duarte`, `Nyman-Beurling`,
  `Weil positivity`, and `Weil criterion`.
- GitHub code query: `RiemannHypothesis repo:leanprover-community/mathlib4`.
- Observation: the query reaches
  `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, which defines the RH statement and basic
  consequences. No exact Li, Baez-Duarte, Li-Weil Gram, or compact Weil criterion theorem was
  found in the pinned tree.

### PrimeNumberTheoremAnd

- Upstream: `AlexKontorovich/PrimeNumberTheoremAnd` at
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`.
- Local vendored source and upstream GitHub code were searched for the same criterion terms and
  for `RiemannHypothesis`.
- Observation: no exact target criterion was found. This project vendors only an audited analytic
  dependency closure; it does not attribute the four equivalence proofs to PNT+.

### Isabelle Archive of Formal Proofs

- Fixed surface: the official AFP catalog and entry pages current on 2026-07-16.
- Catalog/site queries: `Riemann hypothesis`, `Li criterion`, `Nyman-Beurling`, and
  `Weil positivity`.
- Relevant entries surfaced: *The Hurwitz and Riemann zeta Functions* and *Prime Number Theorem
  with Remainder Term*. Their advertised scopes cover zeta foundations, nonvanishing/functional
  equations, PNT, and a zero-free region. No cataloged exact counterpart of the four criteria was
  found.

### Other Lean repositories

- `AlexKontorovich/Lean-RH` (last pushed 2020-10-14) formalizes an RH statement through the
  Dirichlet eta function; its README does not claim the Li, Baez-Duarte, or Weil criteria.
- `lean-dojo/LeanMillenniumPrizeProblems` exposes the Clay/mathlib problem statement and explicitly
  retains a `sorry` placeholder for the prize theorem; it is a statement formalization, not an
  exact criterion counterpart.
- `psinary-sketch/SIDE-li-map/LiLinearMap.lean` proves additivity of an abstract integer-valued Li
  coefficient map. Its own header leaves the analytic identification with xi Taylor coefficients
  outside that file, so it is not the derivative/zero formula or RH iff proved here.
- A broad GitHub code search for `RiemannHypothesis`, `Li coefficient`, `Li criterion`,
  `Nyman Beurling`, and `Weil positivity` in Lean surfaced several unrelated, statement-only,
  synthetic, or axiomatized projects. This broad search is noisy and is recorded only as a lead
  search, not evidence of global absence.

## Primary mathematical references

- Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, Journal of
  Number Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`.
- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI
  `10.1006/jnth.1999.2392`.
- Luis Baez-Duarte, *A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis*,
  arXiv `math/0202141` and Rendiconti Lincei 14 (2003), 5-11.
- Alain Connes and Caterina Consani, *Weil positivity and Trace formula, the archimedean place*,
  arXiv `2006.13771`, especially Appendix C, Proposition C.1.

## Review gates

| Gate | Status on 2026-07-16 | Evidence or next action |
| --- | --- | --- |
| P1 clean-context theorem review | Complete | The separate Sol 5.6 max read-only review found no P0-P2 issue and two P3 attribution/statement-precision issues. See `research/li_weil_sol_max_review_20260717.md`. The 2026-07-13 review remains the evidence for the earlier Baez-Duarte/contour surface. |
| P2 Lean Zulip exposure | Pending human-authored publication | Two in-app browser attempts on 2026-07-16 failed before the Zulip page loaded (the tab remained at `about:blank`). No login state was inspected and no message was sent. Current [mathlib contribution guidance](https://leanprover-community.github.io/contribute/how-to-contribute.html) does not permit LLM-authored GitHub/Zulip comments, so the user must write the request in their own words from the factual theorem names and review evidence in this repository. Record the permanent message URL after publication. |
| P3 bounded novelty audit | Complete within the fixed scope above | Preserve the query scope and the no-priority-claim limitation. |

P1/P2/P3 are output-readiness gates. They do not require approval for a proof campaign. A blocked
Zulip session leaves P2 pending and changes no mathematical status.

The earlier AI-authored announcement draft was removed after reviewing current mathlib policy.
For the human author's factual source packet, use the exact theorem statements above, the two P3
precision findings in `research/li_weil_sol_max_review_20260717.md`, the trust-base paragraph in
the root README, and the permanent repository URL. No generated public message is supplied.
