# R3 Symmetry-Paired Li Zero Formula Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-LI-SYMMETRIC-ZERO-01`

Mode: `INDEPENDENT_AUDIT -> LITERATURE -> FALSIFICATION -> FORMALIZATION`

Route family: R3, Li and Weil positivity.

## Fixed Gap

The preceding campaign proves an all-index formula in terms of the genus-one compensated zero
series and one degree-at-most-one Hadamard polynomial. The next fixed edge is to remove both
artifacts in a mathematically honest convergence convention: pair every multiplicity-bearing zero
`rho` with `1-rho`, prove the resulting raw Li term is summable, identify every derivative-defined
project coefficient with that paired sum, and prove the RH-to-nonnegativity direction for the
whole indexed family.

The project index remains shifted by one: `liCoefficientCandidate n` is classical
`lambda_(n+1)`.

## Primary Literature Alignment

- Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, Journal of
  Number Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`, defines the derivative family
  and proves its positivity criterion.
- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI
  `10.1006/jnth.1999.2392`, treats the zero multiset and the sums
  `1 - (1 - 1/rho)^m` under convergence hypotheses and relates them to Weil positivity.
- Jeffrey C. Lagarias, *Li Coefficients for Automorphic L-Functions*, Annales de l'Institut
  Fourier 57 (2007), 1689-1740, DOI `10.5802/aif.2311`, explicitly defines the zero sums as
  star-convergent, separates the first reciprocal power from the absolutely convergent higher
  powers, and records the multiset symmetry and RH positivity criterion.

The project will use an explicit `rho <-> 1-rho` average. It will not relabel the unpaired raw
series as absolutely convergent.

Novelty classification: `KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`.

## Candidate Generation And Falsification

At most five candidates were considered.

### C1: direct absolute summability of the unpaired raw term

Proposed statement:

```text
Summable (rho |-> 1 - (1 - 1/rho)^m).
```

Falsification: the leading term is `m/rho`. Squared reciprocal summability alone cannot control
it; the model `rho_k = k+1` has a summable squared reciprocal sequence but its `m=1` raw terms are
the harmonic sequence. This rejection must receive a compiled Lean countermodel in the admitted
module.

Decision: rejected.

### C2: multiplicity-preserving reflection equivalence only

Proposed statement: construct an involutive equivalence on the divisor index with value map
`rho |-> 1-rho`.

Falsification: necessary infrastructure, but it neither normalizes the zero sum nor removes the
Hadamard polynomial.

Decision: rejected as a standalone result; retained as a helper.

### C3: paired zero summability without coefficient identification

Proposed statement: prove summability of

```text
1/2 * ((1 - (1 - 1/rho)^m) + (1 - (1 - 1/(1-rho))^m)).
```

Falsification: this would leave the actual derivative-defined project family disconnected from
the sum.

Decision: rejected as a standalone result; retained as a helper.

### C4: all-index paired formula plus RH-forward positivity

Mathematical statement: construct the multiplicity-preserving involution `rho |-> 1-rho`. For
`m=n+1`, define

```text
A_m(rho) = 1 - (1 - 1/rho)^m,
S_n(rho) = (A_m(rho) + A_m(1-rho)) / 2.
```

Prove `sum_rho S_n(rho)` is absolutely/unconditionally summable and

```text
liCoefficientCandidate n = sum_rho S_n(rho)
```

for every `n`. The proof must derive this from the preceding compensated Hadamard formula. It must
average the summable compensated contribution along the reflection equivalence and use
`riemannXi (1-s) = riemannXi s` at `0` and `1` to cancel the derivative of the degree-at-most-one
Hadamard polynomial.

Under RH, `1-rho = conj rho`, and the Bombieri-Lagarias identity gives

```text
S_n(rho) = normSq(A_m(rho)) / 2 >= 0.
```

Conclude for every project index that the coefficient has zero imaginary part and nonnegative
real part.

Proposed Lean surface:

```lean
def riemannXiDivisorZeroReflect : RiemannXiDivisorZeroIndex -> RiemannXiDivisorZeroIndex

noncomputable def riemannXiDivisorZeroReflectEquiv :
    RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex

def liRawZeroTerm (m : Nat) (rho : Complex) : Complex :=
  1 - (1 - 1 / rho) ^ m

def riemannXiSymmetrizedLiZeroTerm
    (n : Nat) (p : RiemannXiDivisorZeroIndex) : Complex := ...

theorem summable_riemannXiSymmetrizedLiZeroTerm (n : Nat) : ...

theorem liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm
    (n : Nat) : ...

theorem RiemannHypothesis.liCoefficientCandidate_eq_tsum_normSq ...

theorem RiemannHypothesis.liCoefficientCandidate_im_eq_zero ...

theorem RiemannHypothesis.liCoefficientCandidate_re_nonneg ...
```

DAG position: after the all-index compensated Hadamard formula and before the reverse
Bombieri-Lagarias/Li positivity-to-RH implication.

RH strength audit: the unconditional paired representation does not constrain zero locations.
The positivity theorem is explicitly conditional on RH. The converse would be RH-equivalent and
is not assumed or claimed.

Decision: **SELECTED**.

### C5: full Li positivity equivalence with RH

Proposed statement: prove

```text
RiemannHypothesis <-> forall n, liCoefficientCandidate n is real and nonnegative.
```

Falsification: this is the exact route endpoint, not a prerequisite. The reverse direction needs
the Bombieri-Lagarias large-index argument or the equivalent unit-disk singularity argument; the
present project does not yet contain either dependency chain.

Decision: deferred as the next possible R3 campaign after C4, subject to independent audit.

## Adversarial Requirements

1. The reflection map must preserve the explicit divisor copy index and analytic multiplicity, not
   merely map zero values as a set.
2. Both `rho != 0` and `rho != 1` must be Lean-proved for every index.
3. The raw unpaired term must not be declared summable.
4. The paired term must be proved summable before its `tsum` is used.
5. The equality with `liCoefficientCandidate n` must hold for every `n`, retaining the
   `lambda_(n+1)` indexing.
6. Cancellation of the Hadamard polynomial must be derived from the functional equation and its
   degree bound, not imposed as a coefficient identity.
7. The fixed point `rho=1/2` must be harmless to the reflection equivalence.
8. An off-critical finite model, for example `rho=1/4` and `m=2`, must demonstrate that paired
   termwise nonnegativity is unavailable without RH.
9. RH-forward positivity must be termwise and exact, not numerical.
10. No reverse Li criterion, zero simplicity, zero ordering, numerical premise, or RH conclusion
    may enter the proof.

## Indivisible Admission And Stop Conditions

The campaign is admitted only if all of the following pass together:

1. the harmonic countermodel and the off-critical sign counterexample compile;
2. the multiplicity-preserving reflection equivalence and its value theorem compile;
3. the compensated finite zero contribution is identified algebraically with the reflected raw
   Li term plus its linear reciprocal compensation for every index;
4. averaging under the reflection equivalence proves paired-term summability;
5. the xi functional equation cancels the Hadamard polynomial contribution;
6. the exact unconditional all-index paired formula compiles;
7. RH turns each paired term into a nonnegative norm square and yields all-index real
   nonnegativity;
8. exact target checks, transitive axiom audit, full build, forbidden-token scans, and diff checks
   pass.

If only the reflection or summability helpers compile, close `NO_PROGRESS`. If the finite
combinatorial identity fails, close `ALGEBRAIC_NORMALIZATION_GAP_IDENTIFIED`. If the polynomial
cancellation fails, close `FUNCTIONAL_EQUATION_NORMALIZATION_GAP_IDENTIFIED`. A successful batch
is `BRIDGE_REDUCED`, with no change to the RH assumption frontier.

## Local Result

Date: 2026-07-15

All eight indivisible admission gates pass locally. The exact compiled endpoint is
`liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm`; under RH the termwise norm-square
identity yields `RiemannHypothesis.liCoefficientCandidate_im_eq_zero` and
`RiemannHypothesis.liCoefficientCandidate_re_nonneg` for every index. The harmonic and
off-critical falsification witnesses also compile.

Classification: `BRIDGE_REDUCED`, `hard_gap_delta=2`, assumption frontier unchanged,
`KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`. Standalone and module builds, exact target checks,
standard-only transitive axiom output, the 8,660-job full build, forbidden scans, and
`git diff --check` pass. Publication and public CI remain pending. The reverse Li positivity
criterion and RH remain unproved.
