# H9 Pólya--Turán Abel Sign Definition Alignment

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-POLYA-TURAN-ABEL-SIGN-AUDIT-01`

Status: `PUBLIC_IMPLEMENTATION_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Source crosswalk

| source object | Lean object | alignment |
| --- | --- | --- |
| Liouville `lambda(n)=(-1)^Omega(n)` | `ArithmeticFunction.liouville` cast by `liouvilleRat` | Mathlib counts prime factors with multiplicity.  Lean checks `lambda(1)=1` and `lambda(2)=-1`. |
| `L(N)=sum_(n<=N) lambda(n)` | `polyaLiouvilleSum N` | `finitePrefixSum` uses `Finset.range N` and evaluates the source term at `n+1`, so the endpoints are exactly `1,...,N`. |
| `T(N)=sum_(n<=N) lambda(n)/n` | `turanLiouvilleSum N` | The same one-indexing is used and division takes place in exact `Rat`; no floating-point approximation occurs. |
| finite Abel summation | `finiteHarmonicWeightedSum_eq_abel` | The terminal term is `A(N)/N`; the remaining coefficients are exactly `1/k-1/(k+1)`. |
| Pólya nonpositivity starts at `N=2` | hypothesis of `turanLiouvilleSum_le_half_of_polya_nonpos` | The initial prefix `L(1)=1` is retained explicitly and contributes `1/2`. |

## Mechanism separation

- Pólya's unweighted sign claim and Turán's harmonic-weighted sign claim are not identified.
- Turán's finite zeta Dirichlet-polynomial route is source-recorded but has no definition in this
  module.
- Haselgrove's disproof and the Borwein--Ferguson--Mossinghoff computation are external historical
  obstructions; they are not replaced by a Lean computation.
- Alkan's all-parameter repaired criteria are RH equivalences and are not project premises.

## Formal result boundary

Lean proves the exact finite transform and an unconditional generic witness.  The witness has
first term `1`, second term `-3`, and every later term zero; hence every prefix from index two
onward equals `-2`, while its second harmonic-weighted sum is `-1/2`.  It is not the Liouville
sequence.  The theorem therefore blocks only a generic inference from prefix nonpositivity to
weighted positivity.

No eventual sign theorem, published large-index certificate, finite zeta-section zero,
eventual-sign-to-RH implication, H9 endpoint, or RH theorem is claimed.

## Lean audit

- Aggregate theorem: `polyaTuranAbelSignAudit_endpoint`.
- Proven Target: `H9.polya-turan.abel-sign-audit`.
- The six selected transitive axiom prints use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden proof-token and declaration scans are empty.
- The full local build passes `8761/8761`.
- Frozen implementation commit `adf2812591fdb0205c2a147ca22f95976421fadc` passed public Lean
  Action run `30184829099`, build job `89747516026`, in `2m33s`.
