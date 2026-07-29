# H2 Classical Detector Dyadic Dichotomy Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01`

Node: `H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `FULL_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_PUBLIC_CI_PENDING`

Public preregistration gate: commit `af32194ba854e6df168f9ec09f1bd8581bbef772`,
Lean Action run `30489281045`, build job `90702801282`, passed in `2m0s`.

## Parent and fixed source

- `parent_closure`: H7 Connes Fourier-topology receipt
  `2408208cbadbf7ba1c5bfe1dae28849a429627fc`, public run `30488165861`, build job
  `90698985577`, passed in `1m35s`.
- `nearest_primary_source`: James Maynard and Kyle Pratt,
  *Half-isolated zeros and zero-density estimates*, Appendix C, proof of Lemma 23,
  <https://arxiv.org/abs/2206.11729>.
- `available_chain`:
  `LeanLab/Riemann/ClassicalZeroDetectorMellin.lean`,
  `LeanLab/Riemann/ClassicalZeroDetectorInverseMellin.lean`, and
  `LeanLab/Riemann/ClassicalZeroDetectorContourShift.lean`.
- `first_open_obstacle`: `OBS-H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01`.

## Source statement

For a nontrivial zeta zero `rho = beta + i*gamma` with `gamma` in `[T,2*T]` and
`beta >= 1/2 + 1/log T`, Maynard--Pratt set

```text
M = 2*T^(1/100),  Y = T^(1/2),
a(n) = sum_{m|n, m<=M} mu(m).
```

The actual smoothed detector satisfies

```text
I(rho)
  = exp(-1/Y)
    + sum_{M<n<K} a(n)*n^(-rho)*exp(-n/Y)
    + farTail
```

for a source cutoff `K` below `Y*(log T)^2`, and also

```text
I(rho) = retainedResidue + shiftedIntegral.
```

After a powers-of-two partition of the finite middle sum, the combined error budget forces

```text
one actual dyadic block is large
  or
the actual shifted Mellin integral is large.
```

The source records thresholds `1/(3*log T)` and `1/3`. The Lean statement may use a stronger
explicit large-`T` threshold or the exact audited number of nonempty dyadic blocks, but it must
include a proved comparison back to the source `log T` scale.

## Required definitions

The implementation should define:

1. `classicalDetectorDyadicBlock`, using the actual
   `classicalDetectorSmoothedTerm M Y rho n` and a powers-of-two block
   `2^j <= n < 2^(j+1)`;
2. a finite source middle range, excluding `n <= M` and a concrete far-tail cutoff;
3. the actual far tail as the remaining `tsum`;
4. source Type-I and Type-II predicates tied respectively to one actual block and
   `classicalDetectorMellinLineIntegral M rho Y (1/2-rho.re)`;
5. an aggregate certificate exposing the decomposition, quantitative error budget, block
   cardinality, and final disjunction.

Equivalent names and a cleaner structured parameter record are allowed. Definitions may not
replace the actual smoothed terms or shifted integral by arbitrary complex variables.

## Full-success criteria

`FULL_SUCCESS` requires all of the following:

1. Prove the divisor-count coefficient estimate
   `norm (classicalDetectorCoefficient M n) <= n.divisors.card`, or a sharper actual
   coefficient estimate sufficient for the source tail.
2. Prove an exact finite-cutoff decomposition of
   `classicalDetectorSmoothedSeries M Y rho` into the `n=1` head, the finite middle range,
   and the actual far tail, under only source-valid positivity hypotheses.
3. Prove that the finite middle range is exactly the sum of the defined dyadic blocks.
   Membership in block `j` must imply `2^j <= n < 2^(j+1)`.
4. Prove an explicit bound on the number of possible or nonempty blocks and connect it to
   `log T` on a concrete large-`T` source regime.
5. Prove an explicit norm bound for the actual far tail from the coefficient estimate and
   exponential smoothing. Merely assuming tail smallness is not full success.
6. Prove the head error `norm(exp(-1/Y)-1)` is small on the same regime.
7. Prove the actual retained residue
   `Y^(1-rho) * Gamma(1-rho) * classicalDetectorMollifier M 1` is small uniformly for
   source-range `rho`, using the compiled Gamma strip decay and finite mollifier bound.
8. Combine the preceding estimates with
   `classicalDetectorCoefficientGap_shifted_identity` to prove an actual Type-I/Type-II
   disjunction. The final theorem must quantify over an actual `IsNontrivialZero rho`.
9. Register one H2 Target as proven, add exact TargetChecks, selected axiom prints, and the
   project-root import.

An eventual large-`T` theorem with a kernel-checked existential threshold is acceptable.
Unexpanded asymptotic notation is not.

## Meaningful partial, falsification, and hard gap

`MEANINGFUL_PARTIAL` requires all of:

- the exact actual-term dyadic decomposition;
- a proved finite block-cardinality theorem;
- at least one of the actual far-tail or retained-residue estimates;
- a theorem reducing the final source disjunction to the one remaining named estimate.

`FALSIFIED_STATEMENT` applies if Lean proves that the source interval, dyadic indexing, stated
threshold, or residue budget is false under the preregistered hypotheses. The corrected
statement and a concrete counterexample or contradiction theorem must be recorded.

`HARD_GAP_REDUCED` applies only if every finite and elementary edge above compiles and the
remaining failure is one exact analytic estimate with its required theorem shape recorded.
Tactic friction is not a hard gap.

## Negative controls

- The generic theorem `exists_large_block_or_remainder` is already compiled and does not close
  this campaign.
- A family of arbitrary blocks is not the source dyadic family.
- Replacing the actual far tail by an assumed error variable is not an analytic tail bound.
- Pointwise Gamma decay without a uniform source-range residue theorem is insufficient.
- Counting all integers up to the cutoff gives the wrong detector scale; powers-of-two
  cardinality is essential.
- The source Type-I/Type-II disjunction is a zero-density input, not a zero-density theorem.

## Audit and publication gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. warning-as-error compile of the new module and registration files;
4. exact TargetChecks and selected standard-only axiom prints;
5. empty forbidden/resource scans;
6. `git diff --check` and full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop only this local campaign and rerank
all historical families.

## Local implementation result

The fixed endpoint is implemented in
`LeanLab/Riemann/ClassicalZeroDetectorDyadicDichotomy.lean`.

Lean now proves:

1. the divisor-cardinality coefficient estimate;
2. the exact actual head/middle/far-tail cutoff;
3. the exact binary-logarithmic block decomposition and block ranges;
4. the explicit actual far-tail estimate
   `K*(1+2Y)*exp(-K/Y)`;
5. the head estimate `norm(exp(-1/Y)-1) <= 1/Y`;
6. a uniform source-range retained-residue majorant tending to zero;
7. the binary block count bound `count <= 3*log T`;
8. eventual admissibility of the literal rounded source scales
   `Y=sqrt T`, `M=floor(2*T^(1/100))`,
   `K=ceil(sqrt(T)*(log T)^2/2)`;
9. the final actual-zero Type-I/Type-II disjunction at those scales.

Aggregate endpoint: `classicalDetectorDyadicDichotomy_endpoint`.

Local classification:
`FULL_SUCCESS / SOURCE_DYADIC_DICHOTOMY_FORMALIZED`.

The result is the finite detector alternative used before the density estimates. It proves no
Type-I or Type-II rarity bound, zero-density exponent, H2 theorem, zero-free region, or RH.

Frozen implementation commit `207953d7cff153eddc017a7d2e2612a786a0c050` passed public Lean
Action run `30491308421`, build job `90709585747`, in `2m18s`. The five proof and registration
files are frozen with an empty diff.
