# H14 x H12 Height-Ten Certificate Preregistration

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Node: `H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Parent: `H12-LM-GLOBAL-INDENTED-COUNT-01`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED / GLOBAL_GOAL_ACTIVE`

## Governing question

Can a proof-producing finite evaluation at height ten certify the exact low-height datum used by
Levinson--Montgomery, without importing numerical tables as axioms, and thereby close their full
analytic count theorem in Lean?

## Exact target

```lean
theorem levinsonMontgomeryHeightTenCertificate_actual :
    LevinsonMontgomeryHeightTenCertificate
```

The target unfolds to both:

```lean
SpeiserStrictNegativeHorizontal 10
```

and

```lean
speiserUpperLeftDerivZeroCount 10 =
  speiserUpperLeftZetaZeroCount 10
```

The preferred stronger finite count result is that both counts are zero. Equality alone is
acceptable only when it is proved for the actual multiplicity-bearing counts.

## Required composition

Full success also registers the consequences

```lean
theorem levinsonMontgomeryTheoremOne_actual :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy

theorem riemannHypothesis_iff_speiserDerivativeZeroFree_actual :
    RiemannHypothesis ↔ SpeiserDerivativeZeroFree
```

using `levinsonMontgomeryTheoremOne_of_heightTenCertificate` and the existing Speiser consumer.
No zero-free or RH premise may occur in the proof of the certificate.

## Source-aligned proof objects

The primary evaluator candidate is a finite Euler--Maclaurin expansion for actual
`riemannZeta`, together with its first and second derivatives and a rigorous coefficientwise
remainder. Every datum consumed by the final checker must reduce to rational inequalities plus
Lean theorems for `exp`, `log`, trigonometric functions, powers, Gamma terms, and Bernoulli
remainders.

The finite proof may use either of two equivalent count mechanisms:

1. cover the complete compact upper-left rectangle below height ten by boxes on which both
   `zeta` and `zeta'` are certified nonzero, proving both actual counts zero;
2. certify boundary nonvanishing and zero winding for their quotient, then use the compiled
   multiplicity-aware finite argument principle to prove equality directly.

The top horizontal sign must be certified uniformly for every `sigma` in `[0,1/2]`, including
both endpoints. A finite sample without a checked derivative or Taylor remainder is insufficient.

## Three attacks

### Attack A: Euler--Maclaurin box certificate

Formalize the Johansson finite expansion and remainder for derivative orders needed by a
Taylor/mean-value enclosure. Generate a finite rational box cover of the top segment and the
low rectangle, then replay every enclosure in Lean.

### Attack B: boundary winding certificate

Avoid two-dimensional zero exclusion. Certify only the four boundary paths for `zeta` and
`zeta'`, compute the quotient winding through a rational polygon or half-plane subdivision, and
use the existing argument principle to recover the actual count offset.

### Attack C: eta and functional-equation evaluator

Use the compiled Hardy--Littlewood eta remainder on the right half of a functional-equation
pair. Obtain derivative tails by Cauchy estimates on explicit disks and certify the same sign and
count statements independently of the Euler--Maclaurin implementation.

These attacks are materially different: full compact nonvanishing, one-dimensional winding, and
a separate analytic expansion.

## Success criteria

Full success requires all of the following:

1. `levinsonMontgomeryHeightTenCertificate_actual` compiles without placeholders;
2. the full theorem-one and Speiser-equivalence compositions compile;
3. the actual functions and actual multiplicity counts are used throughout;
4. every generated numerical enclosure is replayed by Lean rather than trusted as external
   output;
5. exact TargetChecks witness the public statements;
6. selected `#print axioms` output contains no new nonstandard axiom;
7. warning-as-error module, aggregate, target, audit, forbidden-declaration, patch, and full-build
   checks pass.

## Meaningful partial and local stop

A generic interval datatype, a synthetic analytic function, or an uninstantiated checker is
infrastructure only. Meaningful partial progress requires at least one actual source component:

- the complete actual top-edge strict-negativity theorem;
- the actual multiplicity-bearing height-ten count equality; or
- an actual-zeta Euler--Maclaurin theorem with an explicit derivative remainder strong enough to
  discharge a documented finite subcover.

If all three attacks reach distinct first unavailable theorems, record those theorem shapes and
locally stop. The parent H12 node, every evaluator producer, and the persistent RH Goal remain
open for later re-entry.

## Negative controls

- Nonrigorous `mpmath`, Arb, or table values are navigation evidence only.
- The Platt--Trudgian zeta-zero theorem does not imply the zeta-derivative count or the required
  horizontal ratio sign by itself.
- A finite-height certificate is used only because the global analytic reduction already names
  it; no finite-to-global RH promotion is permitted.
- Do not assume RH, Speiser derivative-zero-freeness, CountDichotomy, the height-ten certificate,
  or an equivalent zero-free statement.
- Do not hide analytic evaluation in `axiom`, `opaque`, `unsafe`, `native_decide`, an external
  boolean, or an unverified floating-point result.
- Support cardinality may not replace analytic multiplicity.
- Point samples may not replace a uniform interval theorem.

## Claim boundary

Even full success proves the known Levinson--Montgomery count theorem and the classical Speiser
equivalence. It does not prove `SpeiserDerivativeZeroFree`, H12, or RH. The persistent RH Goal
remains active.

No production or registration file may be edited before this preregistration passes public Lean
Action CI. Protected inherited files remain untouched and unstaged.
