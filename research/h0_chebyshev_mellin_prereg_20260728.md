# H0 Chebyshev--Mellin Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H0-CHEBYSHEV-MELLIN-01`

Selected node: `H0-RIEMANN-VON-KOCH-PSI-MELLIN-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_PENDING`

## Selection reason

The H11 moving-window campaign is publicly closed at final-ledger commit
`a79f218d97f41d27d59ec12293927882d1069283`. Fresh H0/H1/H2/H7/H9/H10/H12 comparison selected
the classical prime-error bridge because the repository has deep explicit-formula machinery but
does not yet contain a source-mapped Target for the Chebyshev `psi` error.

This is not numerical optimization. The fixed question is whether the actual von Mangoldt
partial sums can be connected, with every endpoint convention visible, to the Dirichlet
half-plane selected by a hypothetical `psi(N)-N` error exponent.

## Locked primary sources

1. Bernhard Riemann, "On the Number of Primes Less Than a Given Magnitude" (1859), translated
   by David R. Wilkins. In particular, the Mellin transform of the weighted prime-counting
   function and the subsequent integration by parts.
   <https://www.claymath.org/wp-content/uploads/2023/04/Wilkins-translation.pdf>
2. Helge von Koch, "Sur la distribution des nombres premiers," *Acta Mathematica* 24 (1901),
   159--182. In particular, Sections 2 and 7 and the additional note: differentiation of the
   Euler product, the prime-power logarithmic counting function, and the error term obtained
   from the Riemann zero-location hypothesis.
   <https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5070-11511_2006_Article_BF02403071.pdf>
3. Enrico Bombieri, "The Riemann Hypothesis," official Clay problem description, especially
   formula (5) and the discussion of Riemann's prime-counting transform.
   <https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf>

## Source-exact objects

Use Mathlib's existing definitions without introducing a parallel arithmetic convention:

```text
Chebyshev.psi(x) = sum_{0 < n <= floor(x)} vonMangoldt(n),
L_vonMangoldt(s) = sum_{n >= 1} vonMangoldt(n) / n^s,
L_vonMangoldt(s) = -zeta'(s)/zeta(s) for Re(s)>1.
```

Define the floor-error coefficient

```text
psiErrorCoeff(n) = (vonMangoldt(n) : Complex) - 1.
```

For every natural `N`, its partial sum over `1 <= n <= N` must be exactly

```text
(Chebyshev.psi(N) : Complex) - N.
```

For real `x`, the integral partial sum is `psi(floor x)-floor x`. It differs from the classical
continuous error `psi(x)-x` by exactly `x-floor x`; this correction may not be discarded.

## Pre-proof semantic correction

The first public preregistration passed at commit
`ef2b3e90abebc963522e78ee01a37c7cf5cf1bd9`, Lean Action run `30340366975`, build job
`90214370358`, in `1m55s`. Before any `LeanLab/` edit, the oscillating-sequence adversarial case
exposed a false API identification in block 1:

```text
Mathlib LSeriesSummable f s = Summable (LSeries.term f s),
```

and Mathlib documents this as absolute convergence. A cancellation bound on the complex partial
sums does not imply absolute convergence. It implies convergence only for the naturally ordered
partial sums. The original block 1 is therefore classified
`LIBRARY_SEMANTICS_CORRECTION`; it may not be proved.

The corrected endpoint below uses an explicit ordered partial-sum limit. Compatibility with
Mathlib's `LSeries` is asserted only where absolute convergence is independently available. This
changes no mathematical source claim: it makes the distinction required by Dirichlet's test
visible in Lean.

## Corrected fixed Lean endpoint

Create `LeanLab/Riemann/ChebyshevMellin.lean` and compile all blocks below without placeholders.

1. Define the naturally ordered Dirichlet partial sum
   `sum_{1 <= k <= N} f(k) * k^(-s)` and a predicate or exact `Tendsto` statement for its limit.
   Do not identify this predicate with `LSeriesSummable`.
2. Prove a generic cancellation theorem: if
   `sum_{1 <= k <= n} f(k) = O(n^r)`, `0 <= r`, and `r < Re(s)`, then the naturally ordered
   Dirichlet partial sums converge. The proof must use finite Abel summation and may not replace
   the complex partial sum by the sum of coefficient norms.
3. Identify the exact ordered limit with the Abel/Mellin integral. Prove separately that, under
   `LSeriesSummable f s`, the ordered limit agrees with Mathlib's `LSeries f s`.
4. Prove the exact finite identification between Mathlib's `Chebyshev.psi` and the complex
   von Mangoldt partial sum.
5. Prove the unconditional linear `O(N)` bound needed to recover the von Mangoldt Mellin formula
   on `Re(s)>1`, using Mathlib's compiled Chebyshev bound.
6. Prove
   `L_vonMangoldt(s) = s * integral_{1}^{infinity} psi(x) x^(-s-1) dx`
   for `Re(s)>1`, with the precise set-integral convention.
7. Identify the preceding formula with `-zeta'(s)/zeta(s)` on `Re(s)>1`.
8. Define `psiErrorCoeff`; prove its exact natural partial sum and its exact floor-valued real
   partial sum.
9. Prove on `Re(s)>1` that its absolutely convergent L-series equals
   `-zeta'(s)/zeta(s)-zeta(s)` and equals the corresponding floor-error Mellin integral.
10. Prove the von Koch ordered-convergence bridge: any registered asymptotic hypothesis
   `psi(N)-N = O(N^r)`, with `0 <= r`, implies convergence of the naturally ordered
   error-coefficient Dirichlet partial sums for every `s` with `r < Re(s)`, together with their
   Mellin limit there.
11. Prove the exact floor correction and the bounds `0 <= x-floor(x) < 1` for `0 <= x`.
12. Bundle the generic theorem, the absolute/ordered compatibility theorem, and the actual
    Chebyshev/von Mangoldt statements in one aggregate endpoint certificate.

Names may be adjusted to local APIs. The endpoint may retain natural-number casts or equivalent
`norm` formulations, but it may not assume absolute convergence where only cancellation is
available.

## Adversarial cases

- `N=0`: the finite partial sum is empty while `psi(0)=0`.
- `N=1`: `vonMangoldt(1)=0`, so the error partial sum is `-1`.
- `x` an integer: the floor correction is zero.
- `x` immediately below an integer: the correction remains strictly below one.
- repeated prime powers: each contributes one von Mangoldt coefficient with its logarithmic
  weight.
- `Re(s)=r`: no convergence conclusion is permitted at the boundary.
- `f(n)=1`: the generic theorem recovers only `Re(s)>1`, not the zeta pole.
- an oscillating sequence with bounded partial sums: the generic theorem must retain
  cancellation and yield convergence for `Re(s)>0`.

## Success and falsification criteria

`FULL_SUCCESS` requires all twelve corrected endpoint blocks, an aggregate proven Target, exact
TargetChecks, selected transitive axiom prints, an empty forbidden scan, warning-as-error
compilation, a full build, and independent public CI for preregistration, frozen implementation,
immutable evidence, and final ledger.

`MEANINGFUL_PARTIAL` requires the generic ordered cancellation theorem plus the exact
`psiErrorCoeff` partial-sum identity and its ordered half-plane convergence specialization.

`LIBRARY_SEMANTICS_CORRECTION` is already recorded for the false identification of ordered
convergence with `LSeriesSummable`.

`LIBRARY_BOUNDARY_FOUND` is recorded if the finite Abel theorem compiles but an exact missing
analytic or measurability premise prevents the Mellin equality. The missing premise must be
stated as a theorem-shaped obstacle rather than replaced by an assumption hidden in a
definition.

## Known obstacles and strict boundary

- Mathlib's public `LSeriesSummable_of_sum_norm_bigO` proves absolute convergence and therefore
  does not use the cancellation in `psi(N)-N`. The corrected theorem must use an explicit
  naturally ordered partial-sum limit derived from the compiled finite Abel-summation theorem.
- The zero coefficient is omitted by L-series terms but can affect raw function equalities.
- Complex powers require positivity of the real integration variable and careful real-part
  arithmetic.
- Mathlib's `psi(x)` is right-continuous through `floor(x)`; Riemann/von Koch endpoint averaging
  conventions must not be conflated with this set-integral identity.
- Pointwise L-series convergence in `Re(s)>r` does not by itself prove local uniform convergence
  or holomorphy there.
- The actual reverse von Koch implication still needs analytic continuation of the error
  transform and a zero-exclusion argument using the entire pole-removed zeta function.
- No RH-strength prime-error estimate, H0, H9, or RH is proved in this campaign.

## Mechanical gates

Before proof-source editing:

- publish this corrected docs-only preregistration;
- require public Lean Action CI to pass;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register one aggregate target in `Targets.lean`;
- add exact witnesses in `TargetChecks.lean`;
- print selected transitive axioms in `AxiomsAudit.lean`;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and `unsafe`;
- compile the module with warnings as errors and run the full build;
- freeze the implementation before publishing evidence.

## Stop and successor rule

Stop locally at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`, or a kernel-checked falsification of the
fixed convergence bridge. Local stop returns to fresh cross-family `ROUTE_SELECTION`; it does
not stop the global RH Goal. H9 ordered Franel discrepancy is the leading historical successor,
subject to a fresh rerank. Direct RH attacks and conjecture verification remain open throughout.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; reread current governance, handoff,
  historical census, door atlas, H0/H2/H9/H12 frontiers, the H9 Farey implementation, Mathlib
  Chebyshev/L-series APIs, and the Riemann/von Koch primary sources before selection.
- `global_goal`: active.

## Corrected preregistration public green

- `corrected_preregistration`: commit
  `d718362979fc5e68580af90e1e8a562d5f5b4684` passed public Lean Action run
  `30340685519`, build job `90215366155`, in `1m36s`.
- `production_gate`: opened only after the corrected ordered-convergence endpoint was public
  green.
- `semantic_boundary`: `LSeriesSummable` remains reserved for absolute convergence; the
  cancellation theorem uses an explicit naturally ordered limit.

## Local implementation result

- `module`: `LeanLab/Riemann/ChebyshevMellin.lean`, 527 lines.
- `compiled_endpoint`: all twelve corrected blocks compile. The aggregate theorem is
  `chebyshevMellin_endpoint`.
- `generic_bridge`: `orderedDirichletHasSum_mellin_of_sum_isBigO` sends
  `sum_{1 <= k <= N} f(k) = O(N^r)` to the exact naturally ordered Abel--Mellin limit for
  `0 <= r < Re(s)`, without replacing the complex partial sum by coefficient norms.
- `actual_arithmetic`: the exact Mathlib `Chebyshev.psi`/von Mangoldt partial sum, the
  unconditional `Re(s)>1` Mellin identity, and
  `-zeta'(s)/zeta(s)` identification all compile.
- `error_bridge`: the coefficient `vonMangoldt(n)-1` has exact natural partial sum
  `psi(N)-N`; any registered `O(N^r)` bound gives its naturally ordered Mellin limit throughout
  `Re(s)>r`. The exact real-variable floor correction is also compiled.
- `adversarial_certificate`: the alternating sequence has bounded partial sums and ordered
  convergence at `s=1/2`, while `LSeriesSummable` at the same point is kernel-checked false.
  This prevents later proofs from silently upgrading conditional to absolute convergence.
- `local_audit`: one aggregate proven Target, 13 exact TargetChecks, 11 selected transitive
  axiom prints using only `propext`, `Classical.choice`, and `Quot.sound`; empty
  forbidden/resource scan; warning-as-error module and exact-check compiles; `git diff --check`;
  and full `8779/8779` build.
- `classification`: `CHEBYSHEV_MELLIN_ORDERED_BRIDGE_FORMALIZED`,
  `library_semantics_correction_delta=1`, `historical_route_coverage_delta=1`,
  `hard_gap_delta=0`, `rh_frontier_delta=0`.
- `strict_boundary`: no RH-strength `psi` error estimate, local uniform convergence or
  holomorphy in the enlarged half-plane, reverse zero-exclusion theorem, H0, H9, or RH has been
  proved.
- `next_gate`: freeze and publish the implementation, then require independent public CI.

## Frozen implementation

- `frozen_implementation`: commit `0ff8a577cb4eb247d6cfdbc03d82a5d7dd36707e`.
- `public_ci`: Lean Action run `30342482471`, build job `90220996513`, passed in `2m8s`.
- `proof_freeze`: the 527-line module, aggregate Target, 13 exact TargetChecks, and 11 selected
  axiom prints are frozen.
- `next_gate`: publish docs-only immutable evidence and verify an empty `LeanLab/` diff from the
  frozen implementation.

## Immutable evidence

- `immutable_evidence`: docs-only commit `f038d09b6e3f8d337a59472d4eb8175e48e6f6d1`
  passed public Lean Action run `30342848831`, build job `90222174052`, in `2m20s`.
- `proof_freeze_verified`: the `LeanLab/` diff from frozen implementation
  `0ff8a577cb4eb247d6cfdbc03d82a5d7dd36707e` is empty.
- `local_stop`: `FULL_FIXED_ENDPOINT_SUCCESS / LIBRARY_SEMANTICS_CORRECTION`.
- `remaining`: an RH-strength Chebyshev error estimate, local uniform convergence or
  holomorphy on the enlarged ordered-convergence half-plane, reverse zero exclusion, H0, H9,
  and RH.
- `next_gate`: one docs-only final ledger plus public CI, then fresh cross-family
  `ROUTE_SELECTION`.
