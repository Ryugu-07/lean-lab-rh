# H2 Classical Detector Dyadic Dichotomy Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01`

Node: `H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01`

Classification: `FULL_SUCCESS_LOCAL / SOURCE_DYADIC_DICHOTOMY_FORMALIZED`

Publication status: `PUBLICLY_CLOSED`

## Public preregistration gate

- commit: `af32194ba854e6df168f9ec09f1bd8581bbef772`
- Lean Action run: `30489281045`
- build job: `90702801282`
- result: passed in `2m0s`

No production Lean or registration file was edited before this public gate passed.

## Public implementation gate

- commit: `207953d7cff153eddc017a7d2e2612a786a0c050`
- Lean Action run: `30491308421`
- build job: `90709585747`
- result: passed in `2m18s`

The five proof and registration files are frozen at this implementation commit.

## Public immutable-evidence gate

- commit: `c509cf6f475fa19e86d4734fb39b4b4f740255ef`
- Lean Action run: `30491565903`
- build job: `90710420038`
- result: passed in `1m37s`

The frozen five-file diff remains empty.

## Public final-ledger gate

- commit: `ae35eae20c5f5dcdd2c266e3af4f4fc9dddaa20c`
- Lean Action run: `30491754062`
- build job: `90711045096`
- result: passed in `2m7s`

The closure receipt is the final public gate for this local campaign.

## Compiled endpoint

The 1112-line no-sorry module
`LeanLab/Riemann/ClassicalZeroDetectorDyadicDichotomy.lean` proves:

1. `norm (classicalDetectorCoefficient M n) <= n.divisors.card`;
2. the exact actual head, finite-middle, and far-tail decomposition;
3. the exact sum of binary-logarithmic block fibers;
4. `2^j <= n < 2^(j+1)` for every term contributing to block `j`;
5. the actual far-tail majorant
   `K*(1+2Y)*exp(-K/Y)`;
6. the source head bound and an eventually `1/9` retained-residue bound;
7. at most `3*log T` possible binary blocks when `K<=T`;
8. eventual admissibility of
   `Y=sqrt T`, `M=floor(2*T^(1/100))`, and
   `K=ceil(sqrt(T)*(log T)^2/2)`;
9. the eventual actual-zero Type-I/Type-II disjunction at those literal source scales.

Aggregate endpoint:
`classicalDetectorDyadicDichotomy_endpoint`.

Registered proven Target:
`H2.classical-detector.dyadic-type-dichotomy`.

## Omission-search result

The Maynard--Pratt Appendix C finite detector paragraph has no hidden simple-zero assumption,
no untracked tail premise, and no unproved replacement of the actual shifted integral by an
abstract remainder. The previously compiled inverse-Mellin contour shift supplies exactly the
analytic identity consumed here.

The source cutoff `sqrt(T)*(log T)^2/2` is stronger than the smaller cutoff needed by the
explicit exponential-tail argument. The proof retains the literal source cutoff and verifies
its natural-number rounding, so this slack is recorded without changing the historical
statement.

No overlooked implication from this finite dichotomy directly to RH was found. The next
genuine source inputs are rarity estimates for the actual Type-I dyadic blocks and the actual
Type-II shifted Mellin integrals. Those estimates, rather than the finite partition or error
budget, carry the zero-density content.

## Strict boundary

This campaign proves no:

- Type-I mean-value or large-values estimate;
- Type-II fourth-moment or sparsity estimate;
- zero-density exponent;
- zero-free region;
- H2 theorem;
- Riemann Hypothesis.

## Local audit

- warning-as-error: production module, `Targets.lean`, `TargetChecks.lean`,
  `AxiomsAudit.lean`, and `LeanLab.lean` pass;
- exact TargetChecks: nine;
- selected axiom prints: nine, each using only `propext`, `Classical.choice`, and
  `Quot.sound`;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
- no heartbeat, recursion-depth, timeout, or trace relaxation;
- forbidden/resource scans and `git diff --check`: empty;
- full project build: `8804/8804`;
- protected inherited files: untouched and unstaged.

Freeze and publish the implementation next. After public implementation CI passes, publish
immutable evidence, final ledger, and closure receipt through separate public-green commits.
