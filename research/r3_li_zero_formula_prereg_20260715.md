# R3 All-Index Li Zero Formula Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-LI-ZERO-FORMULA-01`

Mode: `INDEPENDENT_AUDIT -> LITERATURE -> FALSIFICATION -> FORMALIZATION`

Route family: R3, Li and Weil positivity.

## Fixed Gap

The preceding campaign proves a multiplicity-indexed genus-one Hadamard product for the project
`riemannXi` and a pointwise compensated logarithmic-derivative sum away from its zeros. The next
fixed edge is to justify, for every derivative order at once, differentiation of that infinite sum
near `s = 1` and to connect the result to the derivative-defined Li family. Fixed-index coefficient
calculations do not count.

The project definition

```lean
liCoefficientCandidate n =
  iteratedDeriv (n + 1) (fun s : Complex => s ^ n * Complex.log (riemannXi s)) 1 /
    (Nat.factorial n : Complex)
```

is indexed so that `liCoefficientCandidate n` is the classical `lambda_(n+1)`.

## Literature Alignment

- Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, Journal of
  Number Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`, defines
  `lambda_n = 1/(n-1)! * D^n [s^(n-1) log xi(s)]` at `s = 1`.
- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI
  `10.1006/jnth.1999.2392`, uses the multiplicity-bearing zero multiset and the zero expression
  `sum_rho (1 - (1 - 1/rho)^n)` with its convergence convention.
- The immediately available Lean input is the genus-one compensated identity
  `1 / (z - rho) + 1 / rho`, whose terms are absolutely summable from
  `sum_rho |rho|^(-2) < infinity`. The raw classical zero sum is not substituted for this series
  without a separate convergence proof.

Novelty classification: `KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`. No new mathematical Li
criterion is claimed.

## Candidate Generation And Adversarial Tests

At most five candidates were considered.

### C1: all-index Leibniz bridge only

Proposed content: expand `D^(n+1) [s^n log xi(s)]` into derivatives of `logDeriv xi`.

Falsification: mathematically correct and useful, but it leaves every infinite-sum operation
unjustified and is too partial to close the fixed gap.

Decision: rejected as a standalone campaign target; retained as an internal lemma of C5.

### C2: fixed Hadamard polynomial wrapper only

Proposed content: choose one polynomial `P` for the global product and quantify the pointwise
logarithmic-derivative identity over all zero-free points.

Falsification: this is a quantifier-strengthening wrapper around the existing factorization and
does not justify differentiation.

Decision: rejected as a standalone target; retained as an internal lemma of C5.

### C3: raw classical Li zero sum

Proposed content: identify the derivative family immediately with
`sum_rho (1 - (1 - 1/rho)^(n+1))`.

Falsification: the raw series is not absolutely convergent term by term under only squared
reciprocal summability. Dropping the genus-one compensation or silently imposing a symmetric
ordering would be a hidden convergence assumption.

Decision: rejected for this campaign.

### C4: Weil explicit-formula bridge

Proposed content: derive Li coefficients from a complete prime, archimedean, and zero explicit
formula.

Falsification: valid as a separate R5 campaign, but it requires a larger test-function and
distributional infrastructure edge than the present Hadamard derivative bridge.

Decision: deferred.

### C5: all-index compensated derivative-to-zero bridge

Mathematical statement: let the nonzero xi zeros be indexed with analytic multiplicity by the
existing divisor index. For

```text
T_k(rho, z) = (-1)^k k! / (z-rho)^(k+1)
              + (if k = 0 then 1/rho else 0),
```

prove local uniform summability on the zero-free set for every positive derivative order, justify
termwise iterated differentiation at `z = 1`, and prove that one fixed Hadamard polynomial `P`
satisfies, for every `n`,

```text
liCoefficientCandidate n =
  1/n! * sum_(0 <= i <= n) binom(n+1,i) n.descFactorial(i) *
    (D^(n-i) (P') (1) + sum_rho T_(n-i)(rho,1)).
```

Here `D^k (P') (1)` means the iterated derivative of `z |-> P.derivative.eval z`; it is retained
rather than silently discarding the Hadamard exponential factor.

Proposed Lean surface:

```lean
def riemannXiLogDerivZeroDerivativeTerm
    (k : Nat) (p : RiemannXiDivisorZeroIndex) (z : Complex) : Complex := ...

theorem iteratedDeriv_tsum_riemannXiLogDerivZeroTerm (k : Nat) : ...

theorem liCoefficientCandidate_eq_finset_sum_iteratedDeriv_logDeriv (n : Nat) : ...

theorem exists_liCoefficientCandidate_eq_hadamard_zero_formula :
    Exists fun P : Polynomial Complex =>
      P.degree <= 1 /\
      (forall z, riemannXi z = Complex.exp (P.eval z) * ...) /\
      forall n, liCoefficientCandidate n = ...
```

DAG position: after the global xi Hadamard bridge and before either the classical raw-zero-sum
normalization or the all-index Li positivity/RH equivalence.

RH strength audit: C5 does not constrain zero real parts and does not imply RH. It is an exact
representation theorem for the existing xi function. Positivity for all resulting coefficients
would remain RH-equivalent and is not assumed.

Adversarial requirements:

1. `liCoefficientCandidate n` must remain aligned with classical `lambda_(n+1)`.
2. The complex logarithm is used only through its proved analytic branch near `s = 1`.
3. The zero index must preserve analytic multiplicity.
4. `z = 1` must be Lean-proved distinct from every indexed nontrivial zero.
5. The `k = 0` term must retain `1 / rho`; positive orders must differentiate it to zero.
6. Pointwise summability is insufficient: the proof must establish the local uniform hypotheses
   of `iteratedDerivWithin_tsum`.
7. The degree-at-most-one Hadamard polynomial must remain visible in the final theorem.
8. No raw zero ordering, RH, zero simplicity, or numerical premise may enter the proof.

Decision: **SELECTED**.

## Indivisible Admission And Stop Conditions

The campaign is admitted only if all of the following pass together:

1. the exact all-index Leibniz/logarithmic-derivative identity compiles;
2. local uniform summability of every positive-order zero-term derivative is proved from the
   existing squared reciprocal zero summability;
3. `iteratedDerivWithin_tsum` is applied on a proved open zero-free set containing `1`;
4. the explicit `T_k` formula is proved, including the `k = 0` branch;
5. one fixed Hadamard polynomial works for every derivative order and every Li index;
6. the final all-index compensated formula compiles without extra assumptions;
7. exact target checks, transitive axiom audit, full build, forbidden-token scans, and diff checks
   pass.

If only C1 or C2 compiles, the campaign closes `NO_PROGRESS`; those helpers do not independently
reduce the fixed gap. A failure of local uniform convergence closes
`ANALYTIC_INTERCHANGE_GAP_IDENTIFIED`. A successful batch is classified `BRIDGE_REDUCED`, with no
change to the RH assumption frontier.

## Result

Result: `BRIDGE_REDUCED`.

Novelty: `KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`.

Route-local progress: `hard_gap_delta=1`. This counts only the fixed all-index
derivative-to-compensated-zero bridge. The RH assumption frontier is unchanged.

All seven indivisible admission conditions pass in
`LeanLab/Riemann/LiZeroFormula.lean`:

1. `liCoefficientCandidate_eq_finset_sum_iteratedDeriv_logDeriv` proves the all-index finite
   Leibniz expansion with the project indexing retained as classical `lambda_(n+1)`.
2. `summableLocallyUniformlyOn_riemannXiLogDerivZeroDerivativeTerm` proves compact-local uniform
   summability for every positive derivative order. Outside a finite near-zero set, its M-test is
   dominated by `k! * 2^(k+1) * |rho|^(-2)` and uses the previously compiled squared reciprocal
   zero summability.
3. `iteratedDeriv_tsum_riemannXiLogDerivZeroTerm` applies `iteratedDerivWithin_tsum` on the proved
   open set `riemannXiNonzeroSet`, with `1` Lean-proved to belong to that set.
4. `iteratedDeriv_riemannXiLogDerivZeroTerm` proves the exact explicit derivative term and retains
   the `1 / rho` compensation exactly at order zero.
5. `exists_riemannXi_hadamard_iterated_logDeriv_zero_formula` chooses one degree-at-most-one
   Hadamard polynomial for every derivative order.
6. `exists_liCoefficientCandidate_eq_hadamard_zero_formula` combines the whole indexed family in
   one theorem without an extra premise.
7. Exact target checks, transitive axiom audit, standalone and full builds, forbidden-token scan,
   and `git diff --check` pass locally.

The resulting formula is intentionally compensated and multiplicity-bearing. It does not claim
the raw classically ordered zero sum, all-index positivity, Li's equivalence, or RH. The route may
continue only through a precise convergence/normalization theorem for the raw classical zero sum,
an exact Li/RH equivalence, or another comparably global edge. Fixed-index coefficient work remains
inadmissible.

Publication evidence is recorded in the attempts log and `HANDOFF.md` after public CI completes.
