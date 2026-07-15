# R3/R5 Li-Weil Gram Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-R3-R5-LI-WEIL-GRAM-01`

Mode: `ROUTE_MAP -> CONJECTURE_GENERATION -> ADVERSARIAL_TEST -> FORMALIZATION -> INDEPENDENT_AUDIT`

Route family: R3/R5 bridge, Li coefficients as a Weil-positive test-function Gram form.

## Independent Evidence And Route Selection

The previous campaign publicly closed W1b's physical strip algebra. The complete W1c explicit
formula is not admitted as the next indivisible target: Lagarias Appendix A (A.3)-(A.6) requires a
conditionally convergent zero cutoff, unconditional width `delta > 1/2`, local Euler-factor terms,
and cutoff regularization at zero and infinity. A finite zero sum or a formal rearrangement would
not reduce that edge.

Lagarias Theorem 3.1 gives a distinct exact successor in the Li/Weil route. For

```text
G_a(rho) = 1 - (1 - 1/rho)^a,
```

the Weil pairing of `G_a` and `G_b` is a Gram entry, its diagonal is twice the real Li coefficient,
and positivity on the Li class characterizes RH. The project already has the multiplicity-bearing
xi divisor, its `rho |-> 1-rho` involution, summable symmetry-paired Li terms, the exact all-index
Li formula, and the reverse Li/RH criterion. This makes the source theorem a closed formalization
campaign rather than an unchecked zero-sum premise.

Primary source:

- Jeffrey C. Lagarias, *Li coefficients for automorphic L-functions*, Theorem 3.1 and Appendix A,
  <https://www.numdam.org/item/10.5802/aif.2311.pdf>.

## Fixed Definitions

For project index `n`, the source exponent is `n + 1`. Define the reflection-averaged kernel term

```lean
def liWeilGramTerm (n m : Nat) (p : RiemannXiDivisorZeroIndex) : Complex :=
  let rho := riemannXiDivisorZeroValue p
  (liRawZeroTerm (n + 1) rho * liRawZeroTerm (m + 1) (1 - rho) +
    liRawZeroTerm (n + 1) (1 - rho) * liRawZeroTerm (m + 1) rho) / 2
```

and its absolutely convergent divisor sum

```lean
def liWeilGram (n m : Nat) : Complex :=
  tsum (liWeilGramTerm n m)
```

For a finitely supported real coefficient family, define

```lean
def liWeilCombination (c : Nat ->₀ Real) (p : RiemannXiDivisorZeroIndex) : Complex :=
  sum n in c.support,
    (c n : Complex) * liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p)

def liWeilQuadratic (c : Nat ->₀ Real) : Real :=
  sum n in c.support, sum m in c.support,
    c n * c m * (liWeilGram n m).re
```

Minor elaboration changes are allowed. The reflection average, `n + 1` source exponent, real
finite coefficients, and divisor multiplicities are fixed.

## Fixed Endpoint

The indivisible endpoint must prove:

1. `Summable (liWeilGramTerm n m)` for every `n,m`.
2. The pointwise reflection-average identity

```text
K_nm = S_n + S_m - (if n=m then 0 else S_(dist(n,m)-1)),
```

where `S_k` is `riemannXiSymmetrizedLiZeroTerm k`.
3. The exact coefficient formula

```lean
liWeilGram n m =
  liCoefficientCandidate n + liCoefficientCandidate m -
    if n = m then 0 else liCoefficientCandidate (Nat.dist n m - 1)
```

and in particular `liWeilGram n n = 2 * liCoefficientCandidate n`.
4. Under RH,

```lean
liWeilQuadratic c =
  tsum (fun p => Complex.normSq (liWeilCombination c p))
```

with all tsum/finite-sum interchanges justified from the compiled summability.
5. The exact criterion

```lean
RiemannHypothesis <-> forall c : Nat ->₀ Real, 0 <= liWeilQuadratic c
```

The reverse direction must specialize to a genuine one-coordinate `Finsupp.single` and invoke the
compiled all-index Li criterion. The forward direction must use the zero-side norm-square formula,
not the already-known Li nonnegativity theorem alone.

## Candidate Generation And Falsification

### C1: complete W1c zero/prime/pole/archimedean explicit formula

Deferred. The cutoff limit, local terms, width condition, and regularization are one large missing
analytic edge. No existing theorem closes them as one bounded campaign.

### C2: finite-height zero covariance

Rejected. Finite sums are easy but do not establish the conditionally convergent Weil functional
or any source-level positivity criterion.

### C3: a Weil functional on every W1b admissible function

Rejected. Bounded strip analyticity and pointwise Mellin convergence do not by themselves justify
the zero cutoff limit. Admitting continuity of that functional would encode the hard edge.

### C4: reflection-averaged Li-test Gram kernel

Selected. The linear reciprocal divergences cancel in the reflection average, reducing every
entry to a finite combination of the already summable symmetry-paired Li terms. The finite real
span is sufficient for the reverse criterion through its diagonal entries.

### C5: define the Gram matrix directly from Li coefficients

Rejected. This would make the coefficient identity definitional and would not construct the
zero-side Weil pairing or prove its norm-square interpretation under RH.

Adversarial tests for C4:

- test `n=m`, where the distance correction must vanish and the diagonal is exactly `2 lambda`;
- test `(n,m)=(0,1)` and `(0,2)` to catch the project/source index shift;
- preserve multiplicity through the divisor index and its reflection equivalence;
- do not claim summability of an individual raw `G_n(rho)` zero sum;
- prove the reflection average before using tsum linearity;
- under RH derive `1-rho=conj(rho)` from the project RH predicate and prove conjugation of the raw
  test polynomial explicitly;
- test complex coefficient phases; restrict the fixed criterion to real coefficients unless a
  fully Hermitian conjugate pairing is separately proved;
- do not report the resulting RH equivalence as an unconditional proof of either side.

## Strength And Stop Audit

The endpoint is exactly RH-equivalent because all one-coordinate quadratic values recover twice
the real part of every project Li coefficient. It cannot count as `BRIDGE_REDUCED` or RH progress.
Success classification is `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`.

The campaign closes `CONJECTURE_FALSIFIED` if the fixed reflection-average coefficient identity is
false at any tested index, and `NO_PROGRESS` if summability or the RH norm-square identity requires
an unproved explicit-formula premise. Local failure returns to route selection; the persistent RH
Goal remains active.

Verification requires standalone and full builds, exact target witnesses, standard-only transitive
axiom output, empty forbidden/declaration/resource scans, `git diff --check`, and public CI.

## Public Result

The fixed endpoint compiles in `LeanLab/Riemann/LiWeilGram.lean`. Reflection averaging is proved
pointwise before tsum; the raw reciprocal divergence is never admitted. The exact Gram matrix is
expressed in the project's successor-indexed Li coefficients, including compiled `(0,1)`, `(0,2)`,
and diagonal checks. Finite real coefficient sums commute with the divisor tsum by explicit
summability, and under RH the resulting sequence is summable and pointwise `Complex.normSq`.
One-coordinate `Finsupp.single` tests recover the compiled reverse Li criterion.

Standalone/module builds, exact TargetChecks, all 15 public transitive axiom prints, empty
forbidden-token/declaration/resource scans, `git diff --check`, and the 8,665-job full build pass.
Every new theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. Classification is
`KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`.

Implementation commit `2317143e73e1d788d65dcdff9b609a98f8ac60b2` passed public Lean Action CI
run `29415448733`, build job `87352327801`, in 1m48s. Evidence-backfill commit
`89fb947b493c8fd315bbe67a5be8c09fc99cdfa3` passed public Lean Action CI run `29415725269`, build
job `87353260131`, in 1m35s. The campaign is publicly closed; the closure-log CI and final clean
synchronization check remain.
