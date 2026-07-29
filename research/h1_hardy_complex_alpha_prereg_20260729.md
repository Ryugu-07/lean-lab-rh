# H1 Hardy Complex-Alpha Equation Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-COMPLEX-ALPHA-01`

Node: `H1-HARDY-COMPLEX-ALPHA-EQUATION-TWO-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_PENDING`

Public preregistration evidence: commit
`ef1752a44ca1b3242348e7ac40ac4b50529b0efe`, Lean Action run `30415933876`, build job
`90462332932`, passed in `1m37s`.

Frozen implementation evidence: commit
`0f0cb7c2829dd8c35ccf926e0bfb6a79d75147eb`, Lean Action run `30418152861`, build job
`90469028889`, passed in `3m0s`. The five proof and registration files remain unchanged after
that commit.

Immutable evidence: docs-only commit
`389dc3790e2affe3cc6cb7329f78a37cff04023e`, Lean Action run `30418420614`, build job
`90469840559`, passed in `1m56s`. The frozen proof-source diff remains empty.

Final-ledger evidence: docs-only commit
`1de09f4d05dd114a0eca8b89c45fdb0408e6eda7`, Lean Action run `30418635244`, build job
`90470496834`, passed in `1m37s`. The frozen proof-source diff remains empty.

## Fixed historical question

Can Hardy's positive-real Cahen-Mellin equation (1), already compiled for the actual project xi
function, be continued without hidden convergence or branch assumptions to the literal
complex-alpha equation (2) on

```text
hardyAlphaStrip = {alpha : Complex | abs alpha.re < Real.pi / 2}?
```

This is the exact missing bridge between the compiled theorem
`hardyCahenMellinInversion` and the compiled conditional consumer
`hardyXiAbelMomentAmplification_endpoint`.

## Primary source

G. H. Hardy,
*Sur les zeros de la fonction zeta(s) de Riemann*,
Comptes rendus de l'Academie des sciences 158 (1914), 1012--1014:

- <https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN>
- equation (1):
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1014>
- equations (2)--(3):
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1015>

No secondary normalization replaces these displayed formulas.

## Exact mathematical endpoint

The existing definitions are:

```lean
def hardyThetaSeries (y : Complex) : Complex :=
  1 + 2 * tsum fun n : Nat =>
    Complex.exp (-(((n + 1 : Nat) : Complex) ^ 2) * y)

def hardyAlphaStrip : Set Complex :=
  {alpha | abs alpha.re < Real.pi / 2}

def hardyXiInteriorIntegral (alpha : Complex) : Complex :=
  integral (volume.restrict (Set.Ioi 0)) fun t : Real =>
    (Complex.exp (alpha * (t : Complex)) +
      Complex.exp (-alpha * (t : Complex))) *
      (hardyXi (2 * t) : Complex) / (1 / 4 + 4 * t ^ 2)
```

Define the literal source right side:

```lean
def hardyThetaAlphaSide (alpha : Complex) : Complex :=
  (Real.pi : Complex) * Complex.cos (alpha / 4) -
    ((Real.pi / 2 : Real) : Complex) *
      Complex.exp (Complex.I * alpha / 4) *
      hardyThetaSeries
        ((Real.pi : Complex) * Complex.exp (Complex.I * alpha))
```

The full endpoint is:

```lean
theorem hardyCahenMellinEquationTwo
    {alpha : Complex} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyXiInteriorIntegral alpha = hardyThetaAlphaSide alpha
```

Equivalent scalar reassociation is allowed. The actual xi coordinate, denominator, theta
normalization, strip, and constants may not weaken or change.

## Mandatory analytic spine

The endpoint must be supported by the following proved content, with names adjusted only to
local conventions.

### A. Critical-line exponential integrability

For every real `a` with `0 <= a < pi/2`, prove:

```lean
Integrable fun t : Real =>
  Real.exp (a * abs t) * norm (hardyXi (2 * t)) /
    (1 / 4 + 4 * t ^ 2)
```

The proof must use the actual xi factorization. The intended available inputs are:

- `exists_norm_riemannZeta_criticalLine_le_rpow`;
- the exact half-line Gamma norm and positive-strip Gamma-ratio transport used by
  `verticalIntegrable_Gamma_of_pos`;
- elementary absorption of every fixed polynomial by the remaining exponential decay.

A premise that simply assumes xi exponential decay is not accepted as full success.

### B. Parameter-integral analyticity

Use a neighborhood-uniform exponential majorant to prove:

```lean
DifferentiableOn Complex hardyXiInteriorIntegral hardyAlphaStrip
```

Pointwise integrability alone is insufficient. The local dominating exponent must stay strictly
below `pi/2`.

### C. Theta-series analyticity and normalization

Prove summability and termwise analyticity of `hardyThetaSeries` on `Re y > 0`, then prove
analyticity of

```text
alpha |-> hardyThetaSeries (pi * exp(i*alpha))
```

on `hardyAlphaStrip`. Also prove exact agreement with Mathlib's real
`HurwitzZeta.evenKernel 0 x` when `x > 0` and `y = pi*x`.

### D. Imaginary-axis anchor

For every positive real `x`, set `alpha = -I * log x`. Prove:

1. `alpha ∈ hardyAlphaStrip`;
2. `exp(I*alpha) = x`;
3. every complex-power phase in `hardyCahenMellinInversion` equals the corresponding
   exponential factor in the full-line xi integral;
4. actual xi evenness converts the full line to the exact half-line sum
   `exp(alpha*t)+exp(-alpha*t)`;
5. `hardyCahenMellinInversion` becomes
   `hardyXiInteriorIntegral alpha = hardyThetaAlphaSide alpha`.

No theorem with a real-domain `x` argument may be applied directly to a nonreal value.

### E. Identity theorem

Prove `hardyAlphaStrip` is open and preconnected. Promote the imaginary-axis anchor, which has an
accumulation point inside the strip, to all of `hardyAlphaStrip` using Mathlib's analytic identity
theorem.

## Success criterion

`FULL_SUCCESS / HARDY_EQUATION_TWO_FORMALIZED` requires:

1. actual critical-line exponential integrability for every exponent below `pi/2`;
2. analyticity of `hardyXiInteriorIntegral` on `hardyAlphaStrip`;
3. analyticity and exact positive-real normalization of the theta side;
4. branch-correct imaginary-axis equality derived from the compiled equation (1);
5. the exact source equation (2) on the full complex strip;
6. one proven Target with exact statement witnesses;
7. selected `#print axioms` entries showing only the accepted Lean/mathlib trust base;
8. warning-as-error compilation, forbidden scans, `git diff --check`, and a full build;
9. frozen implementation and immutable public CI evidence.

## Meaningful partial

`MEANINGFUL_ANALYTIC_PARTIAL` requires A--D in full and an exact record of the first failed
identity-theorem/domain-connectedness inference. A theorem that assumes exponential integrability,
assumes analyticity, or assumes equation (2) is not a meaningful partial.

If A itself cannot be obtained from the compiled actual Gamma and zeta estimates, the attempt
must stop at the first precise missing inequality. It may not replace A with an abstract decay
interface.

## Falsification and negative controls

The campaign is falsified or narrowed if:

- the source constants do not match the project's `hardyXi`, `riemannXi`, or even-kernel
  normalization;
- the Gamma and zeta estimates leave an exponential rate no stronger than the required weight;
- the theta series is not analytic on the claimed image domain;
- the principal complex power on the positive real axis does not match the alpha exponential;
- evenness changes the factor `pi/2`, `2/pi`, or the half-line normalization;
- equality is known only on a set without an accumulation point in the connected strip;
- totalized integrals make an unproved integrability step appear as a zero equality.

Mandatory controls:

- the existing uniform bound `norm_hardyXi_two_mul_le_phiMass` must be recorded as insufficient
  for nonzero exponential weights;
- no direct complex substitution into `hardyCahenMellinInversion`;
- no boundary value at `abs (Re alpha) = pi/2`;
- no use of `HardyXiAbelMomentLaw` in proving equation (2).

## Assumption and implication frontier

Before this campaign:

```text
actual xi/zeta/Gamma factorization
  + positive-real Hardy equation (1)
  + conditional Abel-moment amplification
  -> open complex-alpha bridge.
```

After full success:

```text
Hardy equation (2) on abs(Re alpha)<pi/2
  -> still open: all-order differentiated identity
  -> still open: tangential theta derivative limit
  -> HardyXiAbelMomentLaw
  -> compiled unbounded critical-line zeros.
```

The campaign does not prove the tangential limit, `HardyXiAbelMomentLaw`, unconditional
infinitely many critical-line zeros, any positive proportion, H1, or RH.

## Historical-omission classification

This is a reconstruction of a known theorem, not a model-original conjecture. The omission audit
tests the suppressed convergence, branch, and identity-theorem steps in Hardy's transition from
equation (1) to equation (2). A successful formalization shortens a fixed historical proof chain;
a failure records the exact suppressed premise or missing library theorem.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1; no serving token budget is exposed.
- `compaction_state`: resumed from a generated summary; canonical governance, `HANDOFF.md`,
  Targets, the current H2 attempt, hard-gap DAG, historical census, H1/H12 route records, and
  Hardy's primary equations were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit and push this docs-only preregistration first. Public Lean Action CI must pass before
editing any `LeanLab/` proof source, target registry, exact check, axiom audit, or root import.
