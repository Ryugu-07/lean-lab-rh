# H0 Chebyshev--Mellin Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H0-CHEBYSHEV-MELLIN-01`

Selected node: `H0-RIEMANN-VON-KOCH-PSI-MELLIN-01`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_PENDING`

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

## Fixed Lean endpoint

Create `LeanLab/Riemann/ChebyshevMellin.lean` and compile all blocks below without placeholders.

1. Prove a generic cancellation theorem: if
   `sum_{1 <= k <= n} f(k) = O(n^r)`, `0 <= r`, and `r < Re(s)`, then the L-series of
   `f : Nat -> Complex` is summable at `s`. The proof must use finite Abel summation and may not
   replace the complex partial sum by the sum of coefficient norms.
2. Combine the generic convergence theorem with `LSeries_eq_mul_integral` to obtain the exact
   Mellin representation from the same partial-sum hypothesis.
3. Prove the exact finite identification between Mathlib's `Chebyshev.psi` and the complex
   von Mangoldt partial sum.
4. Prove the unconditional linear `O(N)` bound needed to recover the von Mangoldt Mellin formula
   on `Re(s)>1`, using Mathlib's compiled Chebyshev bound.
5. Prove
   `L_vonMangoldt(s) = s * integral_{1}^{infinity} psi(x) x^(-s-1) dx`
   for `Re(s)>1`, with the precise set-integral convention.
6. Identify the preceding formula with `-zeta'(s)/zeta(s)` on `Re(s)>1`.
7. Define `psiErrorCoeff`; prove its exact natural partial sum and its exact floor-valued real
   partial sum.
8. Prove on `Re(s)>1` that its L-series equals
   `-zeta'(s)/zeta(s)-zeta(s)` and equals the corresponding floor-error Mellin integral.
9. Prove the von Koch convergence bridge: any registered asymptotic hypothesis
   `psi(N)-N = O(N^r)`, with `0 <= r`, implies summability of the error-coefficient L-series
   for every `s` with `r < Re(s)`, together with its Mellin representation there.
10. Prove the exact floor correction and the bounds `0 <= x-floor(x) < 1` for `0 <= x`.
11. Bundle the generic theorem and the actual Chebyshev/von Mangoldt statements in one aggregate
    endpoint certificate.

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

`FULL_SUCCESS` requires all eleven endpoint blocks, an aggregate proven Target, exact
TargetChecks, selected transitive axiom prints, an empty forbidden scan, warning-as-error
compilation, a full build, and independent public CI for preregistration, frozen implementation,
immutable evidence, and final ledger.

`MEANINGFUL_PARTIAL` requires the generic cancellation theorem plus the exact
`psiErrorCoeff` partial-sum identity and its half-plane convergence specialization.

`LIBRARY_BOUNDARY_FOUND` is recorded if the finite Abel theorem compiles but an exact missing
analytic or measurability premise prevents the Mellin equality. The missing premise must be
stated as a theorem-shaped obstacle rather than replaced by an assumption hidden in a
definition.

## Known obstacles and strict boundary

- Mathlib's public `LSeriesSummable_of_sum_norm_bigO` proves absolute convergence and therefore
  does not use the cancellation in `psi(N)-N`. A new theorem must be derived from the compiled
  finite Abel-summation limit.
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

- publish this docs-only preregistration and route-selection record;
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
