# H2 Maynard--Pratt Type-II Rarity Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Node: `H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `LOCAL_CAMPAIGN_PARKED / EXACT_ANALYTIC_PRODUCER_OPEN`

Result:
`research/h2_maynard_pratt_type_ii_rarity_result_20260730.md`

Public preregistration gate: commit `58a77f7ca4ee0b04dfe4f4653bdc93d8df080be5`,
Lean Action run `30500943541`, build job `90740248215`, passed in `2m1s`.

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

## Source sign audit and corrected form

The arXiv v2 Type-II definition and Appendix C contour both integrate on

```text
Re(s) = 1/2 - beta.
```

Directly writing `s=1/2-beta+i*u` therefore produces

```text
Gamma(1/2-beta+i*u),
```

not the `Gamma(beta-1/2+i*u)` displayed in the proof of Lemma 24.
`MaynardPrattTypeIIRarity.lean` kernel-checks that the two arguments are unequal for
`beta>1/2`. It also kernel-checks the recurrence repair

```text
(beta-1/2) * |Gamma(1/2-beta+i*u)| <= 2
```

for `1/2<beta<1`. Consequently the literal source restriction
`beta>=sigma>=1/2+1/log T` recovers the corrected bound

```text
|Gamma(1/2-beta+i*u)| <= 2*log T.
```

This repairs the pointwise logarithmic estimate but does not by itself prove the uniform
tail truncation, local charge, packing theorem, twisted fourth moment, or rarity exponent.

## Production checkpoint after the source-sign repair

The corrected tail and local charge are now compiled rather than assumed:

- `exists_maynardPrattTypeIIContourNormTailMass_le` gives an explicit integrated
  `exp(-pi*R/4)` tail bound for the actual shifted Mellin integrand.
- `eventually_maynardPrattTypeIIContourNormTailMass_source_le_one` specializes it to the
  literal source scales and `R=(log T)^2`.
- `eventually_one_sixth_le_source_typeIILocalFourthMoment` derives the source local
  fourth-moment lower charge with no tail or moment premise.
- `exists_maynardPrattTypeIISeparated_card_control` proves the finite separated-cover and
  multiplicity bookkeeping from an explicit local occupancy premise.

Thus full-success criteria 1--4 are compiled. Criterion 5 is also now compiled:
`eventually_maynardPrattTypeIILocalMultiplicityCount_source_le` bounds every source local
window by `ceil(30*(log T)^7)`, and
`eventually_exists_maynardPrattTypeIISeparated_source_card_control` composes this with the
multiplicity-aware packing theorem. This uses positivity of the xi reciprocal zero mass at
`2+i*t` and the Euler-product-half-plane logarithmic derivative, so a full
Riemann--von Mangoldt theorem is not a premise.

Criterion 6, the fixed short-Mobius twisted fourth moment, remains open. No Type-II rarity
exponent is claimed at this checkpoint.

The subsequent global charging layer is also compiled:

- `eventually_sum_maynardPrattTypeIILocalFourthMoment_source_le_global` proves that the
  separated radius-`(log T)^2` local windows are disjoint and charge to the literal global
  fourth moment on `[T/2,3T]`;
- `eventually_one_sixth_le_sourceChargeScale_mul_localFourthRoot` keeps the uniform
  `Y^(1/2-sigma)` factor in every local charge;
- `MaynardPrattTypeIISourceTwistedFourthMomentEstimate A` names the exact remaining
  polylogarithmic moment producer for the literal source mollifier; and
- `eventually_exists_typeIISeparated_fullCount_charge_le_of_sourceMomentEstimate` composes
  that single named premise with the discharged local zero count, packing, local charge, and
  global charging theorem.

Thus every structural and measure-theoretic edge through the full Type-II count now compiles.
This is a conditional reduction only: criterion 6 remains open, and the exact factors still
need routine normalization to the criterion-7 exponent display after a moment exponent is
proved. Five exact statement witnesses and seven standard-only axiom prints are registered,
but no Type-II rarity Target is marked proven. Criteria 7--9 and the Type-II rarity claim
remain open.

Implementation commit `b44255fdeb49f12a55214888d26c40d761dfe8e5` passed public Lean
Action run `30505660293`, build job `90754736822`, in `2m49s`. This public-green checkpoint
freezes the conditional reduction before the fixed short-Mobius twisted fourth-moment
attempt. Direct finite mean square, an upper-bound-only approximate functional equation,
Watt's max-coefficient estimate, and the HRS proposition were then audited. None supplies
the required fixed-polylogarithmic moment without returning to deep twisted-moment or
spectral machinery. The local campaign is therefore parked at the exact named moment
producer. The producer, H2 route, and persistent RH Goal remain open.

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
   mollifier-zeta growth needed to control the discarded tail and using the corrected
   negative-real-part Gamma argument.
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
