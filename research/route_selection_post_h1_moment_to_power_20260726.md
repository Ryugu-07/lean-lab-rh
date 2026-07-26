# Route Selection after H1 Moment-to-Power Closure

Date: 2026-07-26

Parent final ledger: `281ba918582707bcfed21920fb3616120d5cd292`

Parent public CI: Lean Action run `30189742343`, build job `89760720303`, passed in `2m2s`.

## Fresh comparison

| candidate | compiled frontier | exact missing object | decision |
| --- | --- | --- | --- |
| H12 Levinson--Montgomery paired mass | The actual zeta and zeta-derivative divisors, multiplicity-bearing upper-left counts, exact-count consumer, xi Hadamard zero sum, reciprocal-square summability, and functional-equation/conjugation multiplicity maps compile. | Reconstruct equations `(2.2)`--`(2.3)` as an actual paired zero mass and prove that eventual negative mass at every integer height forces the linear-density branch `N^-(T)>T/2`. | **Selected.** This is a source-exact part of the still-open analytic count theorem and can use machinery unavailable during the first H12 campaign. |
| H1 Farmer arbitrary-length moments | The full known Bettin--Gonek conditional bridge now compiles. | Prove the open uniform mollified second-moment conjecture for arbitrary positive length exponent. | Direct RH-strength reserve. No remaining known-theorem bridge should be mistaken for progress on the open estimate. |
| H7 Weil ground-state positivity/limit | The literal finite dictionary, admissibility, source calculus, and arithmetic explicit formula compile. | Prove aggregate positivity, inverse/density, simple-even ground states, and a uniform prime-cutoff limit to xi. | High-value reserve, but the next available statements carry essentially RH strength and no new source mechanism was found in this comparison. |
| H2/H11 sparse-exception amplification | Finite localization and horizontal-multiplicity consumers plus generic sparse countermodels compile. | Find an arithmetic theorem that amplifies one actual off-line zeta orbit to a non-sparse defect. | Open discovery reserve; no named source-backed amplifier is currently available. |
| H10 function-field transfer | Finite power-sum rigidity compiles and ordinary infinite reciprocal traces are formally obstructed. | Construct a regularized number-field trace/cohomology object with positivity and a uniform tail. | Structural reserve; a literal finite-to-infinite transfer has already been ruled out. |

## Source re-entry

Levinson and Montgomery, *Zeros of the derivatives of the Riemann zeta-function*, Acta
Mathematica 133 (1974), Theorem 1, proves

```text
N'_-(T) = N_-(T) + O(log T)
```

and an exact-or-linear-density alternative. The first H12 campaign compiled the count objects
and the logical consumer but stopped before the source analytic theorem.

The new attack isolates the mechanism on pages 51--52, equations `(2.2)`--`(2.3)`. For
`s=sigma+i*t`, functional-equation partners `rho=beta+i*gamma` and
`1-conj(rho)=1-beta+i*gamma` give a real paired kernel. The resulting mass is a sum over actual
multiplicity-bearing xi zeros. If this mass is negative, at least one left zero satisfies

```text
|t - gamma| < 1/2.
```

When this happens at every sufficiently large integer height, the half-unit neighborhoods are
disjoint and supply linearly many distinct upper-left zeros. This is the source step producing
the dense branch of `LevinsonMontgomeryCountDichotomy`.

## Material difference

The 2026-07-23 H12 campaign did not possess the later xi zero-sum infrastructure now used by the
H7 explicit-formula work: locally uniform compensated Hadamard sums, reciprocal-square
summability, multiplicity-preserving divisor permutations, finite norm cutoffs, and robust
finite/infinite sum decomposition.

This campaign does not retry the old abstract count consumer. It attacks the actual infinite
zero-pair mass and the integer-to-count passage. Raw `sum 1/(s-rho)` is not treated as absolutely
summable; the real functional-equation pairs must be shown summable through compensated terms
and reciprocal-square control.

## Claim boundary

Success proves the source paired-mass identity, the near-zero localizer, and the dense count
branch from eventual negative paired mass. It does not yet prove:

- the full logarithmic count bound;
- the implication from `Re(zeta'/zeta)>=0` to negative paired mass, including Gamma estimates;
- the low-height sign certificate at `t=10`;
- the indented critical-line argument principle;
- the full `LevinsonMontgomeryCountDichotomy`;
- Speiser's equivalence without the two registered analytic premises;
- RH.

The next campaign decision must be based on the exact first remaining source edge, not on API
momentum.
