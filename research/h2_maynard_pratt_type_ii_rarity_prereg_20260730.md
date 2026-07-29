# H2 Maynard--Pratt Type-II Rarity Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Node: `H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTRATION_LOCAL / PRODUCTION_LOCKED`

## Parent and fixed sources

- `parent_closure`: H1 eta-primitive mean-square receipt
  `dd593af9c0a838016f4ca954221dc7408a9d662a`, public run `30500121527`, build job
  `90737729961`, passed in `1m56s`.
- `nearest_primary_source`: James Maynard and Kyle Pratt,
  *Half-isolated zeros and zero-density estimates*, Lemma 24 and Appendix C,
  <https://arxiv.org/abs/2206.11729>.
- `twisted_moment_sources`: Hughes and Young,
  *The twisted fourth moment of the Riemann zeta function*,
  <https://arxiv.org/abs/0709.2345>; Bettin, Bui, Li, and Radziwill,
  *A quadratic divisor problem and moments of the Riemann zeta-function*,
  <https://arxiv.org/abs/1609.02539>.
- `compiled_parent`:
  `LeanLab/Riemann/ClassicalZeroDetectorDyadicDichotomy.lean`, especially
  `ClassicalDetectorTypeII` and
  `eventually_classicalDetectorSource_typeILog_or_typeII`.
- `selected_obstacle`: `OBS-H2-MAYNARD-PRATT-TYPE-II-RARITY-01`.

## Source statement

Let `R_II(sigma,T)` count Type-II nontrivial zeros
`rho=beta+i*gamma`, with multiplicity, such that

```text
beta >= sigma,  gamma in [T,2T].
```

Maynard--Pratt Lemma 24 proves

```text
R_II(sigma,T) <= T^(2*(1-sigma)) * (log T)^O(1).
```

For each Type-II zero, Appendix C first derives

```text
T^(sigma/2-1/4) / log T
  <= C * integral_(|u| <= (log T)^2)
      |M(1/2+i*gamma+i*u) * zeta(1/2+i*gamma+i*u)| du,
```

then Holder gives

```text
T^(2*sigma-1) / (log T)^10
  <= C * integral_(|u| <= (log T)^2)
      |M(1/2+i*gamma+i*u) * zeta(1/2+i*gamma+i*u)|^4 du.
```

After extracting a `(log T)^3`-separated family and charging local windows to
`[T/2,3T]`, the proof invokes the specific twisted fourth-moment bound

```text
integral_(T/2)^(3T)
  |M(1/2+i*t) * zeta(1/2+i*t)|^4 dt
    <= C * T * (log T)^A.
```

Here `M` is the actual project mollifier with length
`classicalDetectorSourceM T = floor(2*T^(1/100))`.

## Required definitions

The implementation should define, with equivalent names allowed:

1. a finite multiplicity-bearing Type-II zero count in the source rectangle, using
   `riemannXiZeroMultiplicity` rather than an unweighted set cardinality;
2. the actual critical-line twisted value
   `classicalDetectorMollifier (classicalDetectorSourceM T) (1/2+i*t) *
    riemannZeta (1/2+i*t)`;
3. source local and global fourth-moment integrals;
4. an explicit separation predicate for selected zero ordinates;
5. an aggregate certificate exposing the local charge, packing bound, specific global moment,
   and final rarity exponent.

Definitions must use the existing actual Type-II shifted Mellin integral. They may not replace
it with an arbitrary complex variable.

## Full-success criteria

`FULL_SUCCESS / MAYNARD_PRATT_LEMMA24_FORMALIZED` requires all of:

1. Prove finiteness and M0 alignment of the positive-height Type-II zero collection, with
   analytic multiplicities preserved.
2. Prove the exact change of variables from the existing shifted Mellin line integral to the
   source critical-line `u` integral.
3. Prove an explicit Gamma-decay truncation to `|u| <= (log T)^2`, including the actual
   mollifier-zeta growth needed to control the discarded tail.
4. Derive the source local fourth-moment lower charge from Type-II largeness by explicit
   integral inequalities.
5. Prove a multiplicity-aware separated-subfamily or bounded-overlap theorem sufficient to
   charge all Type-II zeros to one global interval. Any local zero-count input used here must
   itself be compiled, not silently imported as `O(log T)`.
6. Prove the specific source-mollifier twisted fourth-moment upper bound with explicit
   eventual constants and log exponent. Assuming this bound is not full success.
7. Combine the preceding theorems to obtain an eventual explicit form of
   `R_II(sigma,T) <= C*T^(2*(1-sigma))*(log T)^A` throughout the source range.
8. Compose this bound with the compiled actual Type-I/Type-II dichotomy and state exactly
   that only the Type-I rarity branch remains.
9. Register one H2 Target as proven, add exact TargetChecks, selected axiom prints, and the
   project-root import.

Unexpanded asymptotic notation is not accepted in the Lean endpoint.

## Omission probe

The cited Hughes--Young and Bettin--Bui--Li--Radziwill theorems prove much more than the
consumer uses: arbitrary-polynomial asymptotics at lengths at least `T^(1/11-epsilon)`,
whereas this campaign needs one upper bound for one Mobius polynomial of length
`2*T^(1/100)`.

The proof attempt should therefore test, in order:

1. direct expansion plus an existing finite Dirichlet-polynomial mean value;
2. a source-valid upper-bound-only approximate functional equation;
3. only then the full cited twisted fourth-moment machinery.

A successful weaker producer is the historical omission sought by this campaign.

## Meaningful partial, falsification, and hard gap

`MEANINGFUL_PARTIAL / SOURCE_REDUCTION_FORMALIZED` requires all of:

- the actual multiplicity-bearing Type-II count;
- the exact shifted-integral-to-local-fourth-moment charge;
- the separated or bounded-overlap global charging theorem;
- a final theorem deriving the source rarity exponent from separately named local-zero-count
  and specific twisted-fourth-moment premises.

This classification proves no rarity estimate unless those premises are discharged.

`FALSIFIED_STATEMENT` applies if the literal source count, interval, multiplicity convention,
Gamma truncation, or exponent arithmetic fails under the preregistered hypotheses. The
corrected theorem and a kernel-checked counterexample or contradiction must be recorded.

`HARD_GAP_REDUCED` applies only when the exact remaining producer has a fixed theorem shape
and every elementary, measure-theoretic, packing, and exponent edge before and after it
compiles. Tactic friction is not a hard gap.

## Negative controls

- A generic finite-set fourth-moment Markov inequality does not connect to actual zeta zeros.
- An assumed twisted fourth-moment bound is not Maynard--Pratt Lemma 24.
- Counting distinct zero locations without analytic multiplicity is not the source count.
- Pointwise Gamma decay without a uniform tail theorem is insufficient.
- A density bound for Type-II zeros does not exclude one Type-I zero.
- Section 8 bow configurations lie in the Type-I/clustering obstruction and are not removed
  by this campaign.
- Lemma 24 is a zero-density input, not H2, a zero-free region, or RH.

## Audit and publication gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. warning-as-error compile of proof and registration files;
4. exact TargetChecks and selected standard-only axiom prints;
5. empty forbidden/resource scans;
6. `git diff --check` and full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop only this local campaign and rerank
all historical families.
