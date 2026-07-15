# R3 Xi Hadamard Campaign

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-XI-HADAMARD-01`

Route: R3, Li and Weil positivity

Result: `BRIDGE_REDUCED`

`hard_gap_delta=3` for the separately inventoried order-one growth, global genus-one canonical
product, and multiplicity-indexed compensated zero-sum prerequisites.

RH assumption frontier: unchanged.

Novelty: `KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`.

## Fixed Target

The preregistered batch required one global bridge from the preceding project xi divisor to an
order-one Hadamard factorization. Admission required the complete pinned upstream source closure,
exact equality of the two xi definitions, exact multiplicity-index/nontrivial-zero alignment,
squared reciprocal summability, the genus-one global product, and the away-from-zeros
logarithmic-derivative sum. A finite-ball factorization, an order bound alone, or a partial source
import did not count.

## Candidate Audit

1. **Finite-ball factorization:** rejected. Mathlib's finite-support zero/pole extraction is local
   and does not yield global summability or a Li-ready product.
2. **Order-one growth alone:** rejected as artificially partial after the pinned source audit found
   the complete factorization dependency graph.
3. **Choice-based natural enumeration:** rejected. The exact divisor index already carries
   multiplicity, while a sequence equivalence is unnecessary for the divisor-indexed theorem.
4. **R5 explicit formula:** deferred as a distinct prime/archimedean/test-space campaign.
5. **Global genus-one xi bridge:** selected and compiled.

## Source Audit

Pinned source:
`AlexKontorovich/PrimeNumberTheoremAnd@d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, Apache-2.0.

Terminal module:
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean`.

The recursive custom dependency closure has 61 modules and 14,368 lines. Twenty-four were already
present byte-for-byte. The campaign added exactly the 37 missing modules. A post-build comparison
against a detached checkout of the pinned commit reports `byte_mismatches=0`. The full closure has
no code occurrence of `sorry`, `admit`, `axiom`, `native_decide`, or a resource-limit relaxation.

The upstream terminal theorem batch compiled in this project with 3,683 jobs before the local
bridge was written.

## Adversarial Results

1. **Distinct xi declarations.** The upstream theorem concerns `Complex.riemannXi`, whereas the
   project carrier is `LeanLab.Riemann.riemannXi`. Lean proves function equality by unfolding the
   two definitions and normalizing the field expression. No theorem is transferred by name alone.
2. **Origin exclusion.** The canonical product indexes only nonzero divisor points. For every
   project nontrivial zero, the existing exact zero theory proves it is nonzero, so Lean constructs
   the required subtype index.
3. **Multiplicity loss.** The index fiber is
   `Fin (Int.toNat (MeromorphicOn.divisor riemannXi univ rho))`. Lean proves this `Int.toNat` is
   exactly `riemannXiZeroMultiplicity rho`; the product therefore repeats zeros according to the
   same analytic multiplicity as the preceding global divisor.
4. **One-way support alignment.** Lean proves both directions: every index value is
   `IsNontrivialZero`, and every `IsNontrivialZero` has an index value equal to it.
5. **Wrong genus.** No genus-zero product is inferred. The admitted theorem is genus one and uses
   summability of squared reciprocal zero norms.
6. **Dropped denominator condition.** The project log-derivative theorem assumes
   `not IsNontrivialZero z`; this is converted in Lean to inequality from every divisor-index value.
7. **Discarded exponential factor.** The factorization retains `exp (P z)` with
   `degree P <= 1`; no claim removes the Hadamard polynomial.
8. **Li overclaim.** The convergent compensated term is
   `1/(z-rho) + 1/rho`. This does not by itself justify the all-index Li zero sum or differentiation
   under an infinite sum. Those remain open.

## Compiled Results

New project module: `LeanLab/Riemann/LiHadamard.lean`.

- `riemannXi_eq_complex_riemannXi`
- `riemannXiZeroDivisor_eq_complex_riemannXi_divisor`
- `riemannXi_divisor_toNat_eq_zeroMultiplicity`
- `riemannXiDivisorZeroIndex_val_isNontrivialZero`
- `exists_riemannXiDivisorZeroIndex_of_isNontrivialZero`
- `exists_riemannXiDivisorZeroIndex_val_iff`
- `riemannXi_entireOfOrderAtMost_one`
- `summable_riemannXiDivisorZeroIndex_norm_inv_sq`
- `exists_riemannXi_hadamard_factorization`
- `summable_riemannXi_logDerivTerms_of_not_isNontrivialZero`
- `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum`

The key product theorem is

```lean
theorem exists_riemannXi_hadamard_factorization :
    exists P : Polynomial Complex, P.degree <= 1 /\ forall z : Complex,
      riemannXi z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ z
```

and the value alignment is

```lean
theorem exists_riemannXiDivisorZeroIndex_val_iff (rho : Complex) :
    (exists p : Complex.Hadamard.divisorZeroIndex0 riemannXi Set.univ,
      Complex.Hadamard.divisorZeroIndex0_val p = rho) <-> IsNontrivialZero rho
```

The ASCII spellings in these display snippets stand for the compiled Unicode identifiers in the
source file.

## Literature Alignment

- Li, 1997, DOI `10.1006/jnth.1997.2137`, defines the derivative family and its RH-equivalent
  positivity.
- Bombieri-Lagarias, 1999, DOI `10.1006/jnth.1999.2392`, treats the zero multiset with multiplicity
  and its convergence conventions.
- The imported Lean theorem is an existing finite-order Hadamard formalization from the pinned
  `PrimeNumberTheoremAnd` source. This campaign claims project alignment, not a new mathematical
  factorization theorem.

## Verification

- Pinned terminal module build: pass, 3,683 jobs.
- `rtk lake env lean LeanLab/Riemann/LiHadamard.lean`: pass, no warnings.
- Exact `Targets` and `TargetChecks`: pass.
- Transitive `AxiomsAudit`: pass; all seven selected declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Full `rtk lake build`: pass, 8,658 jobs.
- Closure byte audit: 61 modules, zero mismatches against the pinned commit.
- Placeholder, explicit axiom, `native_decide`, and resource-relaxation source scans: empty.
- `rtk git diff --check`: pass.

Implementation commit `406fef704202777a6510a9eddd69a402075d31f6` is public on
`Ryugu-07/lean-lab-rh`. Lean Action CI run `29394659365`, build job `87285308740`, completed
successfully in 3m12s.

## Progress Accounting

Campaign classification: `BRIDGE_REDUCED`.

Route-local `hard_gap_delta=3`: order-one xi growth, the multiplicity-indexed global genus-one
canonical product, and the compensated log-derivative zero-sum convergence are now compiled and
aligned with the project carrier. The RH assumption frontier is unchanged.

Still open are a correctly defined all-index Li coefficient family, the rigorous bridge from its
derivative definition to the global zero expression (including infinite-sum differentiation and
convergence conventions), all-index positivity, and the exact Li/RH equivalence in Lean.

Next state: `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. A further R3 campaign must target the
all-index derivative-to-zero bridge or an equally precise global edge; fixed-index coefficient
calculations remain inadmissible.
