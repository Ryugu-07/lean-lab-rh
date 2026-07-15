# R3 Xi Hadamard Campaign Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-XI-HADAMARD-01`

Mode: `INDEPENDENT_AUDIT -> LITERATURE -> FALSIFICATION -> DISCOVERY`

Route family: R3, Li and Weil positivity.

## Fixed Gap

The preceding xi-divisor campaign aligned the support and finite analytic multiplicities of the
project-local `riemannXi` exactly with `IsNontrivialZero`. The next fixed R3 gap is global: local
finiteness alone gives neither a convergent product nor a zero sum. Li's zero-side formula needs a
global entire-function growth bound, a multiplicity-aware canonical product, and a convergent
logarithmic-derivative zero sum.

This campaign attempts that entire global edge. It does not attempt the Li coefficient definition,
the derivative-to-zero identity, positivity for any infinite family, or RH.

## Independent Source Audit

The pinned Apache-2.0 source commit
`AlexKontorovich/PrimeNumberTheoremAnd@d963a6e694a05cd82e5f9b9ae7f4d94123e85393`
contains `RiemannZetaHadamard.lean`. Its exact xi results include:

- order at most one for the entire `Complex.riemannXi`;
- summability of squared reciprocal nonzero divisor indices;
- a genus-one divisor-indexed Hadamard product with degree-at-most-one exponential polynomial;
- the corresponding convergent logarithmic-derivative zero sum away from zeros.

The recursive custom dependency closure has 61 modules and 14,368 lines. Twenty-four modules are
already present byte-for-byte in this repository; 37 are missing. The closure scan has no code
occurrence of `sorry`, `admit`, `axiom`, `native_decide`, or resource-limit relaxation. Presence in
the upstream source is not admission: all 37 missing modules must be snapshotted, compiled against
this project's pinned Lean/mathlib, and transitively axiom-audited.

Source:
`https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/d963a6e694a05cd82e5f9b9ae7f4d94123e85393/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean`.

## Closest Mathematical Literature

- Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, Journal of
  Number Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`. Li's coefficient family is
  defined by derivatives of `log xi`, and its zero-side expression uses all xi zeros with
  multiplicity.
- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI
  `10.1006/jnth.1999.2392`. Their zero-multiset formulation makes convergence and multiplicity
  part of the global criterion, not optional local bookkeeping.
- The upstream Lean source specializes the finite-order Hadamard strategy to xi and cites Tao's
  finite-order factorization theorem together with the classical treatments of Titchmarsh,
  Edwards, Boas, and Levin.

Novelty classification: `KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`. No new mathematical result
is claimed for the upstream factorization. The project-specific contribution is the formally
checked identification of its xi and multiplicity index with the already audited local RH carrier.

## Candidate Generation And Falsification

At most five candidates were considered.

### C1: global genus-one xi Hadamard bridge

Mathematical statement: the project-local `riemannXi` is the upstream entire xi, has order at most
one, has a multiplicity-indexed nonzero zero set with summable squared reciprocal norms, and admits
the exact genus-one Hadamard and logarithmic-derivative formulas. The underlying index values are
exactly the nonzero project `IsNontrivialZero` points, repeated according to analytic multiplicity.

Proposed Lean surface:

```lean
theorem riemannXi_eq_complex_riemannXi :
    riemannXi = Complex.riemannXi

theorem riemannXi_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : Real) riemannXi

theorem riemannXiDivisorZeroIndex_val_isNontrivialZero
    (p : Complex.Hadamard.divisorZeroIndex0 riemannXi Set.univ) :
    IsNontrivialZero (Complex.Hadamard.divisorZeroIndex0_val p)

theorem exists_riemannXiDivisorZeroIndex_of_isNontrivialZero
    {rho : Complex} (hrho : IsNontrivialZero rho) :
    Exists fun p : Complex.Hadamard.divisorZeroIndex0 riemannXi Set.univ =>
      Complex.Hadamard.divisorZeroIndex0_val p = rho

theorem summable_riemannXiDivisorZeroIndex_norm_inv_sq :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex0 riemannXi Set.univ =>
      norm (Complex.Hadamard.divisorZeroIndex0_val p) ^ (-2 : Int))

theorem exists_riemannXi_hadamard_factorization :
    Exists fun P : Polynomial Complex => P.degree <= 1 /\
      forall z, riemannXi z = Complex.exp (P.eval z) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ z
```

The final declarations may follow the exact upstream power syntax rather than this schematic
surface, but they must retain the local function and the multiplicity-indexed divisor.

DAG position: R3, immediately after the global zero divisor and before the Li coefficient
derivative-to-zero identity.

RH strength audit: C1 does not imply RH. The product includes every nontrivial zero wherever it is.
Its polynomial and zero sum encode the existing entire function without constraining zero real
parts.

Adversarial tests:

- The upstream `Complex.riemannXi` and project-local `LeanLab.Riemann.riemannXi` are distinct
  declarations. Algebraic similarity is insufficient; Lean must prove function equality.
- The canonical product excludes the origin. Lean must prove every nontrivial zero is nonzero and
  every divisor index value is a project nontrivial zero.
- A support equality does not by itself preserve multiplicity. The index must use the same
  `MeromorphicOn.divisor`, and both directions of value coverage must be proved.
- Genus zero is not inferred. The admitted source theorem uses genus one and squared reciprocal
  summability.
- The logarithmic-derivative identity is valid only away from every indexed zero. No denominator
  side condition may be dropped.
- No `Nat` enumeration is inferred without an actual equivalence; the divisor-index type is the
  primary exact carrier.
- The degree-at-most-one exponential polynomial is retained. It may not be silently discarded.

Decision: **SELECTED**. It closes the precise global edge left open by the previous campaign and is
strictly stronger than a finite-ball factorization.

### C2: finite-ball linear factorization

Rejected after audit. Mathlib's finite-support extraction can factor xi on each ball, but the
result is local and does not provide global zero summability or the Li zero sum. C1 subsumes the
useful content and removes a larger fixed gap.

### C3: order-one growth only

Rejected as an artificially partial batch. The same audited source closure already supplies the
canonical product and logarithmic derivative that are the reason the growth theorem matters.

### C4: choose a `Nat` enumeration of all zeros

Rejected. Enumeration without the canonical-product summability and multiplicity index would be
weaker, and existence of a sequence equivalence is not needed for the exact divisor-indexed sum.

### C5: begin the Weil explicit formula

Deferred. The prime and archimedean terms form a separate R5 campaign. They are not prerequisites
for admitting the already exact R3 Hadamard bridge.

## Admission And Stop Conditions

The batch is indivisible and is admitted only if all of the following hold together:

1. the 37 missing files are byte-identical to the pinned Apache-2.0 upstream commit;
2. the entire 61-module closure contains no forbidden proof placeholder, project axiom, native
   decision shortcut, or resource-limit relaxation;
3. the upstream terminal Hadamard module compiles against this project's pinned toolchain;
4. Lean proves equality of the two xi functions;
5. Lean proves divisor-index values are exactly project nontrivial zeros and preserves the common
   multiplicity-bearing divisor;
6. Lean transports order-one growth, squared reciprocal summability, the global genus-one product,
   and the away-from-zeros logarithmic-derivative sum to the project-local xi;
7. exact target checks, transitive axiom prints, the full project build, source scans, and diff
   checks pass.

If the pinned closure fails to compile, the campaign closes as `DEPENDENCY_GAP_IDENTIFIED`; no
partial imported helper counts as progress. If function or divisor alignment fails, it closes as
`REPRESENTATION_MISMATCH`. If all conditions pass, the intended classification is
`BRIDGE_REDUCED`, with the order-growth, canonical-product, and zero-summability R3 prerequisites
removed. The derivative-defined Li family, derivative-to-zero identity, all-index positivity, and
RH remain open.

## Result

Result date: 2026-07-15

Classification: `BRIDGE_REDUCED`

Route-local `hard_gap_delta=3`; the global RH assumption frontier is unchanged.

All seven admission conditions pass. The 61-module upstream closure is byte-identical to the
pinned commit and compiles locally; the 37 newly snapshotted files contain no forbidden proof or
resource declaration. `LeanLab/Riemann/LiHadamard.lean` proves exact equality of the two xi
functions, exact divisor-fiber multiplicity, both directions of divisor-index value coverage,
order-one growth, squared reciprocal summability, the no-monomial genus-one Hadamard product, and
the compensated logarithmic-derivative zero sum away from `IsNontrivialZero`.

Exact target checks, standard-only axiom output, the 8,658-job full build, source scans, closure
byte audit, and `git diff --check` pass. This result does not define or prove positivity of the full
Li coefficient family and does not prove RH. Publication evidence is recorded in
`attempts/r3_xi_hadamard_campaign.md`. Implementation commit
`406fef704202777a6510a9eddd69a402075d31f6` passed public Lean Action CI run `29394659365`, build
job `87285308740`, in 3m12s. Evidence-backfill commit
`ffbd4967d3e220593bbbcaa1c63ffbe37dea4282` passed run `29394898804`, build job `87286063151`, in
1m28s.
