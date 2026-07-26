# H9 Farey--Mobius--Weyl Transform Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-FAREY-MOBIUS-WEYL-01`

Selected node: `H9-FAREY-MOBIUS-WEYL-TRANSFORM-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION / PRODUCTION_GATE_CLOSED`

## Parent public closure

The preceding Hardy critical-line sign campaign is publicly closed. Final-ledger commit
`24567b9a7bd2baae902c83ffbb1b2281a676a074` passed Lean Action run `30213706063`, build job
`89824117700`, in `1m50s`. That campaign closed only the exact project-xi real coordinate and
sign-change consumer. It did not supply Hardy's transform, endpoint signs, critical-line
infinitude, H1, or RH.

## Selection rationale

Fresh cross-family selection compared Hardy's original transform, the open Riesz decay and
continuation, non-unit Redheffer estimates, H2 density, H7 spectral convergence, H10
function-field transfer, H11 pair correlation, H12 Speiser, and the still-absent
Farey--Franel--Landau branch.

Farey is selected because it is a canonical RH-equivalent family with no production Lean
representation, while its first exact arithmetic mechanism can be isolated without assuming an
ordered enumeration or a discrepancy bound. For the source convention

```text
0 < numerator <= denominator <= N, gcd(numerator, denominator) = 1,
```

Mobius inversion converts every reduced-fraction test sum into a finite Mertens-weighted sum over
all numerator blocks. At the frequency-one exponential test, the full numerator blocks vanish
except at denominator one, so the Farey Weyl sum is exactly the finite Mertens sum.

This is the arithmetic backbone behind the later equidistribution and discrepancy criteria. It
is not a numerical-constant optimization and does not create a new route. Formalizing it audits
the endpoint convention, duplicate representation, finite rearrangement, and exact location of
the unresolved RH-strength estimate.

## Primary-source anchors

J. Kanemitsu and M. Yoshimoto, *Farey series and the Riemann hypothesis*, Acta Arithmetica 75
(1996), 351--374, DOI `10.4064/aa-75-4-351-374`:

`https://matwbn.icm.edu.pl/ksiazki/aa/aa75/aa7544.pdf`

The paper defines its Farey fractions by reduced pairs `0 < b <= c <= x`. Its Lemma 3 gives the
finite Mobius/Mertens transform

```text
sum_{rho <= xi} f(rho)
  = sum_{n <= x} M(floor(x/n)) V_xi(n),
```

where `V_xi(n)` is the complete numerator-block sum. Definition 1 and Lemma 2 isolate
Mertens-weighted sums whose square-root estimates are equivalent to RH. Proposition 3 and its
corollaries specialize the transform to exact Farey identities.

J. Franel, *Les suites de Farey et le probleme des nombres premiers*, Gottinger Nachrichten
(1924), 198--201:

`https://eudml.org/doc/59156`

Franel is retained as the historical discrepancy anchor. This campaign reconstructs the exact
finite arithmetic transform before any discrepancy estimate.

## Exact fixed endpoint

The implementation must prove all of the following.

1. Define source-aligned positive numerator blocks

   ```text
   fareyNumerators(q) = {a | 1 <= a <= q and gcd(a,q)=1}
   fareyPairs(N) = {(a,q) | 1 <= q <= N and a in fareyNumerators(q)}.
   ```

   Pair orientation may follow Lean ergonomics, but the rational value must be `a/q`.

2. Prove exact membership facts. Every registered pair has positive numerator and denominator,
   numerator at most denominator, denominator at most `N`, and coprimality. Conversely, every
   pair satisfying those source conditions is registered.

3. Prove reduced positive pairs represent the same rational only when both numerator and
   denominator agree. Register explicitly that `0/1` is excluded and `1/1` is included exactly
   once when `1 <= N`.

4. Prove the denominator-block cardinality is `Nat.totient q` for positive `q`, and hence

   ```text
   card(fareyPairs(N)) = sum_{1 <= q <= N} Nat.totient(q).
   ```

5. For `f : Rat -> Complex`, define the complete block and the actual reduced Farey sum:

   ```text
   V_f(n) = sum_{1 <= a <= n} f(a/n)
   F_N(f) = sum_{(a,q) in fareyPairs(N)} f(a/q).
   ```

6. Prove the exact `xi=1` Kanemitsu--Yoshimoto Lemma 3 transform:

   ```text
   F_N(f)
     = sum_{1 <= n <= N} (finiteMertens (N / n) : Complex) * V_f(n).
   ```

   A merely abstract Mobius inversion theorem, without the actual Farey pair sum on the left,
   does not satisfy this endpoint.

7. Define the literal frequency-one atom

   ```text
   e(x) = Complex.exp(2 * Real.pi * Complex.I * x).
   ```

   Prove every complete block with denominator greater than one sums to zero and the
   denominator-one block sums to one.

8. Deduce both exact specializations:

   ```text
   sum_{a in fareyNumerators(q)} e(a/q) = moebius(q)
   F_N(e) = finiteMertens(N),
   ```

   with the appropriate integer-to-complex coercions.

9. Compile edge checks at `N=0`, `N=1`, and at least one nontrivial order. The checks must detect
   accidental inclusion of `0/1`, duplicate inclusion of `1/1`, reversed pair coordinates, and
   a missing terminal numerator.

The primary Target must aggregate the generic transform, pair normalization, cardinality, and
frequency-one Mertens specialization. A standalone root-of-unity sum or totient count does not
satisfy the campaign.

## Proposed Lean surface

Names may change only to match project style; mathematical content may not weaken.

```lean
def fareyNumerators (q : Nat) : Finset Nat :=
  (Finset.Icc 1 q).filter fun a => Nat.Coprime a q

def fareyPairs (N : Nat) : Finset (Nat x Nat) := ...

def fareyValue (p : Nat x Nat) : Rat :=
  p.1 / p.2

def fareyFullBlock (f : Rat -> Complex) (n : Nat) : Complex := ...

def fareySum (f : Rat -> Complex) (N : Nat) : Complex := ...

theorem farey_sum_eq_mertens_transform (f : Rat -> Complex) (N : Nat) :
    fareySum f N =
      sum n in Finset.Icc 1 N,
        (finiteMertens (N / n) : Complex) * fareyFullBlock f n := ...

def fareyFrequencyOne (x : Rat) : Complex :=
  Complex.exp (2 * Real.pi * Complex.I * x)

theorem farey_frequency_one_sum_eq_finiteMertens (N : Nat) :
    fareySum fareyFrequencyOne N = (finiteMertens N : Complex) := ...
```

## Intended proof route

1. Use finite intervals and filters, not an assumed ordered Farey sequence.
2. Express the coprime indicator as the divisor sum of the Mobius function.
3. Reindex `a=d*k`, `q=d*n` under positive bounds and exchange only finite sums.
4. Group by `n`; the remaining `d <= N/n` coefficient is exactly `finiteMertens(N/n)`.
5. Prove rational representation uniqueness by cross multiplication plus coprimality.
6. Prove the complete exponential block by a finite geometric sum and exact periodicity of the
   complex exponential.
7. Obtain the primitive denominator-block identity either by the compiled generic transform at
   fixed denominator or by Mobius inversion of the complete blocks.
8. Specialize the global transform; only `n=1` survives.

The proof may introduce reusable finite reindexing lemmas, but every such lemma must remain
mathematically attached to the registered Farey objects.

## Falsification tests

- `SOURCE_CONVENTION`: exclude `0/1`; include `1/1` once.
- `POSITIVE_DENOMINATOR`: no rational division by zero is hidden in a totalized Lean operation.
- `REDUCED_ONLY`: all Farey pairs are coprime.
- `NO_DUPLICATE_VALUES`: equal reduced positive rationals have identical pairs.
- `TERMINAL_NUMERATOR`: complete blocks use `1 <= a <= n`, not `0 <= a < n`, unless an exact
  periodic reindexing theorem is also compiled.
- `MERTENS_FLOOR`: the coefficient is exactly `M(floor(N/n))`, represented by natural division.
- `MOBIUS_CAST`: integer signs survive the cast to `Complex`.
- `ROOT_SUM_N_ONE`: the `n=1` block is one, not zero.
- `ROOT_SUM_N_GT_ONE`: the vanishing theorem has the necessary positive/nonunit hypotheses.
- `NO_SORTING_SMUGGLE`: no theorem about the `nu`-th ordered Farey fraction is claimed.
- `NO_DISCREPANCY_SMUGGLE`: an exact Weyl sum at one frequency is not called a discrepancy
  estimate or equidistribution theorem.
- `NO_RH_PROMOTION`: the exact identity supplies no Mertens growth bound.

## Success and classification

Success requires every fixed endpoint, one proven aggregate Target, exact TargetChecks, selected
transitive axiom prints with standard axioms only, empty forbidden scans, warning-as-error
compilation, full build, and all public CI gates.

Expected classification:

- `result=FAREY_MOBIUS_WEYL_TRANSFORM_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `farey_normalization_delta=1`;
- `farey_mertens_transform_delta=1`;
- `farey_discrepancy_delta=0`;
- `mertens_growth_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

If the generic transform cannot be compiled, record the strongest exact pair-level theorem and
the first precise reindexing or library obstruction as `PARTIAL / BLOCKER_EXPOSED`. The
frequency-one identity alone is not full campaign success.

## Production and stopping gates

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI.

The local campaign stops when the fixed endpoint is proved, falsified, or reduced to a precise
Mathlib or mathematical obstruction. Success returns to fresh cross-family route selection
before choosing an ordered Farey discrepancy successor, Hardy's transform, or another historical
family. Local STOP does not close H9 or the active RH Goal.
