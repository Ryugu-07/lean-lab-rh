# R3 Xi Zero-Divisor Campaign Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-XI-DIVISOR-01`

Mode: `LITERATURE -> FALSIFICATION -> DISCOVERY`

Route family: R3, Li and Weil positivity. This is a different route family from the closed R1
sparse Gram and target-obstruction campaigns.

## Fixed Gap

The Li/Hadamard inventory records that the project has no global zero carrier for `riemannXi` with
multiplicity and locally finite support. Li coefficients ultimately require a zero sum with
multiplicity; fixed low-index calculations do not supply that carrier.

This campaign attempts exactly the divisor/local-multiplicity subedge. It does not attempt a
Hadamard product, a convergent global zero enumeration, a Li zero-sum identity, positivity, or RH.

## Closest Literature

- Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, Journal of
  Number Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`. Li defines the full coefficient
  family by derivatives of `log xi`; positivity of every coefficient is the RH-equivalent edge.
- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI
  `10.1006/jnth.1999.2392`. Their zero-sum and Guinand-Weil formulations require zeros counted with
  multiplicity.
- Mathlib's `MeromorphicOn.divisor` is a locally finite divisor implementation, but it has not been
  aligned in this project with the exact `riemannXi`/`IsNontrivialZero` predicates.

Novelty classification: `KNOWN_STRUCTURE_PROJECT_ALIGNMENT`. No new mathematical result is
claimed.

## Candidate Generation And Falsification

At most five candidates were considered.

### C1: exact xi zero divisor with multiplicity

Mathematical statement: the entire, nonzero function `riemannXi` has a globally defined locally
finite divisor. Its value at `s` is the finite natural order of vanishing, its support is exactly
the set of project nontrivial zeta zeros, and multiplicity is invariant under `s |-> 1 - s`.

Proposed Lean surface:

```lean
def riemannXiZeroMultiplicity (s : Complex) : Nat :=
  analyticOrderNatAt riemannXi s

def riemannXiZeroDivisor : Function.locallyFinsupp Complex Int :=
  MeromorphicOn.divisor riemannXi Set.univ

theorem isNontrivialZero_iff_riemannXi_eq_zero (s : Complex) :
    IsNontrivialZero s <-> riemannXi s = 0

theorem riemannXiZeroDivisor_apply (s : Complex) :
    riemannXiZeroDivisor s = (riemannXiZeroMultiplicity s : Int)

theorem support_riemannXiZeroDivisor :
    Function.support riemannXiZeroDivisor = {s | IsNontrivialZero s}

theorem riemannXiZeroMultiplicity_pos_iff (s : Complex) :
    0 < riemannXiZeroMultiplicity s <-> IsNontrivialZero s

theorem riemannXiZeroMultiplicity_one_sub (s : Complex) :
    riemannXiZeroMultiplicity (1 - s) = riemannXiZeroMultiplicity s
```

DAG position: R3, before any Hadamard product, zero sum, or global Li-criterion statement.

RH strength audit: C1 does not imply RH. It records every nontrivial zero wherever it lies.

Adversarial tests:

- `s = 0` and `s = 1`: already known to have `riemannXi = 1/2`.
- Negative even integers: zeta vanishes there, but xi must not. The proof must reflect them by the
  functional equation to real part greater than one and use unconditional zeta nonvanishing.
- Infinite order: `analyticOrderAt = top` would mean local identically-zero behavior. The proof
  must use the analytic identity theorem and `riemannXi 1 = 1/2` to exclude it globally.
- Divisor poles: the divisor must be nonnegative because `riemannXi` is entire.
- Multiplicity symmetry: support symmetry alone is insufficient; analytic order must be transported
  through the affine map `s |-> 1 - s`, whose derivative is nonzero.
- No sum over the divisor and no enumeration may be inferred from local finiteness alone.

Decision: **SELECTED**. It closes one explicitly inventoried prerequisite and has exact hostile
edge cases that Lean can adjudicate.

### C2: enumerate all zeros by `Nat`, repeated by multiplicity

Rejected for this campaign. A choice-based enumeration could be manufactured after countability,
but without a canonical ordering or summability theorem it would not yet support the Li zero sum.

### C3: prove order-one growth and a global Hadamard product

Rejected as the immediate target. The project lacks a reusable finite-order entire-function
factorization theorem, and the analytic growth estimate is a substantially larger source batch.

### C4: prove a local generating-function identity for all derivative-defined Li coefficients

Deferred. It gives a full index syntactically but still has no zero-side interpretation; selecting
it first would leave the identified divisor gap untouched.

### C5: begin the complete Weil explicit formula

Rejected for this campaign. Prime, archimedean, zero, and test-space terms form a much larger R5
frontier and cannot be honestly reduced to a small generic positivity lemma.

## Admission And Stop Conditions

The batch is indivisible: C1 is admitted only if all of the following compile together without
placeholders or nonstandard axioms:

1. nonvanishing on `Re(s) > 1` and at every trivial-zero point;
2. exact `IsNontrivialZero <-> riemannXi = 0`;
3. finite analytic/meromorphic order at every point;
4. a global locally finite divisor with exact natural-multiplicity values;
5. exact support and compact-local finiteness;
6. functional-equation invariance of multiplicity.

If the trivial-zero exclusion or finite-order proof fails, no divisor-support claim is admitted and
the campaign closes as `NO_PROGRESS` or `CONJECTURE_FALSIFIED` according to the mathematical cause.
If all items pass, the intended classification is `BRIDGE_REDUCED`: the divisor/local-multiplicity
prerequisite is closed, while Hadamard growth, global zero summability, the Li zero-sum identity,
all-index positivity, and RH remain open.

## Result

Result date: 2026-07-15

Classification: `BRIDGE_REDUCED`

`hard_gap_delta=1` for the fixed R3 divisor/local-multiplicity prerequisite; the global RH
assumption frontier is unchanged.

All six admission conditions compile in `LeanLab/Riemann/LiZeroDivisor.lean`. In particular, Lean
proves the negative-even trivial zeta zeros are not xi zeros, rules out infinite local analytic
order, identifies every divisor value with a natural zero multiplicity, identifies the support
exactly with `IsNontrivialZero`, proves finite intersection with every compact set, and transports
multiplicity under `s |-> 1-s`. Exact TargetChecks, transitive axiom prints, the 8620-job full
build, forbidden scans, and `git diff --check` pass.

No Hadamard product, global zero enumeration or sum, Li positivity, or RH is inferred. Publication
evidence is recorded in `attempts/r3_xi_zero_divisor_campaign.md`. Implementation commit
`15e30c800e39d904b1623d5e8efcb40864e18655` passed public Lean Action CI run `29392983909`, build
job `87280263113`, in 2m2s.
