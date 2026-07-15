# R5 Weil Finite Gaussian Test-Core Preregistration

Campaign: `CAMPAIGN-20260716-R5-WEIL-FINITE-GAUSSIAN-TEST-CORE-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

## Route Boundary

The predecessor campaign proves the complete xi explicit formula for every individual probe

```text
G_(a,b)(s) = exp(a * (s - 1/2)^2) * cosh(b * (s - 1/2)),
             a > 0, b real.
```

The new endpoint is not another probe. It is the algebraic test core formed by arbitrary finite
complex superpositions of these probes. For a finite index type `ι`, positive widths `a i`, real
modulations `b i`, and coefficients `w i`, every term in the final formula must be applied to the
directly synthesized packet

```text
G(s) = sum_i w_i * G_(a_i,b_i)(s).
```

This is the finite test space that a later Schwartz-density and tempered-distribution campaign can
close and extend by continuity. This campaign does not assert that the packet space is dense.

Closest primary source:

- J. Arias de Reyna, Theorems 1 and 3 and the finite Hermite-function core used before continuous
  extension to Schwartz space: https://arxiv.org/abs/2402.10604

The source's RH-equivalent temperedness assertion is not imported. The completed single-probe
formula supplies every analytic and arithmetic input used here.

## Candidate Audit

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: fixed-width Gaussian-cosine span is dense in even Schwartz space | No mathematical counterexample was found. A standard Hermite or annihilator proof should work, but Mathlib currently exposes neither Hermite completeness in Schwartz topology nor compactly supported smooth density there. Proving the required analysis is several independent infrastructure edges. | Preserve as the next density campaign; do not weaken it to L2 density. |
| C2: complete finite Gaussian packet formula | Finite superposition preserves every absolute summability and integrability hypothesis. Empty, singleton, zero-coefficient, repeated-parameter, and reordered packets are harmless. Direct zero and prime `tsum`s and the direct archimedean integral prevent a representation-only restatement. | Select. |
| C3: L2 density of Gaussian probes | L2 density does not determine a tempered distribution and cannot extend the explicit formula on Schwartz space. | Reject as insufficient for G6. |
| C4: temperedness of the prime/archimedean quasicrystal | Arias de Reyna proves this is equivalent to RH. Treating it as an input would hide the target theorem. | Reject as a premise. |

## Pre-Admission Falsification

1. The empty packet must reduce to `0 = 0`.
2. A singleton packet with coefficient `1` must reduce exactly to
   `symmetricGaussianXi_arithmetic_explicit_formula`.
3. Zero coefficients and repeated parameter pairs must not change the synthesized functions.
4. Complex coefficients are required; restricting to positive or real coefficients would not
   produce the linear test core used by distribution theory.
5. Every `a i` must remain strictly positive. A single `a i = 0` destroys the compiled absolute
   zero and prime summability arguments.
6. No positivity statement is admitted. Complex superposition does not preserve pointwise sign.

## Fixed Definitions And Endpoint

Harmless naming and algebraic reassociation are allowed. The final theorem must retain direct
packet-level zero, archimedean, and prime expressions rather than merely summing the already known
equalities on the outside.

```lean
def riemannXiSymmetricGaussianPacketWeight
    {ι : Type*} [Fintype ι] (a b : ι -> Real) (w : ι -> Complex)
    (z : Complex) : Complex :=
  sum i, w i * riemannXiSymmetricGaussianWeight (a i) (b i) z

def symmetricGaussianPacketVonMangoldtWeight
    {ι : Type*} [Fintype ι] (a b : ι -> Real) (w : ι -> Complex)
    (n : Nat) : Complex :=
  sum i, w i * symmetricGaussianVonMangoldtWeight (a i) (b i) n

def symmetricGaussianXiPacketArchimedeanIntegral
    {ι : Type*} [Fintype ι] (a b : ι -> Real) (w : ι -> Complex)
    (c : Real) : Complex :=
  integral fun y : Real =>
    riemannXiSymmetricGaussianPacketWeight a b w (c + y * Complex.I) *
      logDeriv Complex.GammaR (c + y * Complex.I)

def symmetricGaussianXiPacketPoleFactor
    {ι : Type*} [Fintype ι] (a b : ι -> Real) (w : ι -> Complex) : Complex :=
  sum i, w i * (Real.exp (a i / 4) * Real.cosh (b i / 2) : Real)

theorem symmetricGaussianXiPacket_arithmetic_explicit_formula
    {ι : Type*} [Fintype ι]
    (a b : ι -> Real) (w : ι -> Complex)
    (ha : forall i, 0 < a i) {c : Real} (hc : 1 < c) :
    (Real.pi : Complex) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          riemannXiSymmetricGaussianPacketWeight a b w
            (riemannXiDivisorZeroValue p)) =
      2 * (Real.pi : Complex) * symmetricGaussianXiPacketPoleFactor a b w +
        symmetricGaussianXiPacketArchimedeanIntegral a b w c -
          tsum (symmetricGaussianPacketVonMangoldtWeight a b w)
```

The module must additionally prove absolute summability of both direct packet series,
integrability of the direct packet archimedean integrand, exact finite-sum interchange for all
three terms, and the singleton compatibility theorem.

## Proof DAG

1. Define the four packet-level objects over an arbitrary finite index type.
2. Prove pointwise finite-sum algebra and absolute summability of the synthesized zero family.
3. Prove integrability of the synthesized archimedean integrand and commute its finite sum with
   the full-line integral.
4. Prove absolute summability of the synthesized prime-power family and commute its finite sum
   with `tsum`.
5. Sum the compiled single-probe explicit formulas and rewrite every side to the direct packet
   expression.
6. Prove singleton compatibility independently and audit empty/zero packets through exact checks.

## Stop Conditions

- Do not shrink the endpoint to an outer `Finset.sum` of known formulas.
- Do not replace direct zero or prime `tsum`s by definitions that already contain componentwise
  `tsum`s.
- Do not replace the direct archimedean integral by a definition that already contains the sum of
  component integrals.
- Do not claim Schwartz density, temperedness, Weil positivity, or RH.
- Reject any project axiom, `sorry`, `admit`, `native_decide`, unsafe/opaque declaration, or
  resource-limit relaxation.
- If finite-sum interchange cannot be closed for two independent proof approaches, classify this
  local campaign as `NO_PROGRESS` and return to route selection.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: a two-parameter family of individually evaluated Gaussian probes; no
  algebraic test core
- `hard_gap_after`: if successful, the complete explicit formula on the finite complex span of
  those probes
- `hard_gap_delta`: one algebraic test-core subedge of G6; zero for density, G7, and RH
- `assumption_frontier_after`: Schwartz/Hermite density, continuity of the explicit-formula
  functionals, tempered extension, local regularization, Weil positivity, and RH remain
- `expected_classification`: `BRIDGE_REDUCED`

## Verification Gate

No new theorem becomes a later premise until the standalone module, exact Targets and
TargetChecks, selected transitive axiom prints, forbidden token/declaration/resource scans,
`git diff --check`, full project build, public commit, and public CI all pass.

## Local Outcome

Proof Attempt A reaches the fixed endpoint without weakening the statement.
`WeilFiniteGaussianTestCore.lean` proves direct packet-level absolute zero and prime summability,
GammaR integrability, all three exact finite interchanges, and
`symmetricGaussianXiPacket_arithmetic_explicit_formula`. Independent singleton and empty-packet
theorems compile. The standalone module, exact Targets and TargetChecks, six selected axiom
prints, forbidden declaration/token/resource scans, `git diff --check`, and the 8,672-job full
build pass. Every selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Classification is `BRIDGE_REDUCED`; publication and public CI remain before closure.

Implementation commit `736901e03f08ccb399e4ec5f84980a641cb4e344` passed public Lean Action CI
run `29445905312`, build job `87456185038`, in `2m33s`. Immutable evidence backfill and that
commit's own public CI remain before closure.
