# H1 Hardy Tangential Theta Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-TANGENTIAL-THETA-01`

Node: `H1-HARDY-TANGENTIAL-THETA-LIMIT-01`

Primary mode: `LITERATURE`

Status: `PREREGISTRATION_PUBLIC_GREEN / IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_PENDING`

Public preregistration evidence: commit
`648d8e8140f1af0ea5726cf030b8ab4bc4dc8581`, Lean Action run `30429533400`, build job
`90503309053`, passed in `2m43s`.

Frozen implementation evidence: commit
`75f5c575b2c3f050f0e5703efb5ce6851d97775c`, Lean Action run `30435633763`, build job
`90522592740`, passed in `2m17s`. The six proof and registration files remain unchanged after
that commit.

Immutable evidence: docs-only commit `85f0ae62feb457961a3e71ca15db50fa195ce459`, Lean Action run
`30436167642`, build job `90524303908`, passed in `2m7s`. The frozen six-file diff remains empty.

## Fixed historical question

Can Hardy's equation (3) and its tangential theta limit be reconstructed from the compiled
equation (2), without assuming `HardyXiAbelMomentLaw`, an endpoint Lebesgue integral, a custom
summability axiom, or a non-source normalization?

## Primary source

G. H. Hardy,
*Sur les zeros de la fonction zeta(s) de Riemann*,
Comptes rendus de l'Academie des sciences 158 (1914), 1012--1014:

- <https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN>
- equation (1):
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1014>
- equations (2)--(3), tangential limit, and source summability argument:
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1015>

The facsimile, rather than the text transcription alone, fixes the `t^(2p)` factor in equation
(3). The source's last theta term is differentiated `2p` times and is asserted to tend to zero
as `alpha -> pi/2` from below.

## Existing compiled endpoints

The left endpoint is:

```text
hardyEquationTwo :
  alpha in hardyAlphaStrip ->
  hardyEquationTwoLeft alpha = hardyThetaAlpha alpha.
```

The project already proves:

- exact `exp(-(pi/2)|t|)` Gamma decay for the actual xi factor;
- every polynomially weighted exponential majorant inside the strip;
- analyticity of the actual xi integral and theta side;
- Hardy equation (2) throughout `abs (Re alpha) < pi/2`.

The right consumer is:

```text
infinite_criticalLineZeros_of_hardyXiAbelMomentLaw :
  HardyXiAbelMomentLaw ->
  Set.Infinite {t : Real |
    IsNontrivialZero (hardyCriticalLinePoint t)}.
```

No theorem currently constructs `HardyXiAbelMomentLaw`.

## Proposed Lean statements

The production names may be adjusted to existing namespace conventions, but the mathematical
content is fixed:

```lean
def hardyThetaBoundaryTerm (alpha : Complex) : Complex :=
  ((Real.pi / 2 : Real) : Complex) *
    Complex.exp (Complex.I * alpha / 4) *
      hardyThetaAlpha alpha

theorem hardyXiInteriorIntegral_iteratedDeriv_real
    (p : Nat) {alpha : Real} (halpha : |alpha| < Real.pi / 2) :
    iteratedDeriv (2 * p) hardyXiInteriorIntegral (alpha : Complex) =
      (hardyXiAbelMoment alpha p : Complex)

theorem tendsto_iteratedDeriv_hardyThetaBoundaryTerm
    (p : Nat) :
    Tendsto
      (fun alpha : Real =>
        iteratedDeriv (2 * p) hardyThetaBoundaryTerm (alpha : Complex))
      (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2)))
      (nhds 0)

theorem hardyXiAbelMomentLaw_unconditional :
    HardyXiAbelMomentLaw

theorem infinite_criticalLineZeros_hardy :
    Set.Infinite {t : Real |
      IsNontrivialZero (hardyCriticalLinePoint t)}
```

The final theorem must be a direct composition with the existing audited consumer. The theorem
proving the law may not assume the law, any equivalent endpoint limit, or eventual critical-line
sign changes.

## Planned proof chain

### A. Actual integral differentiation

Define the order-`m` alpha derivative of the actual interior kernel explicitly. Prove by induction
that it is the `m`-th derivative and dominate the next derivative locally by

```text
constant * |t|^(m+1) * hardyXiExponentialWeight a t
```

for some `a < pi/2`. The already compiled polynomial-weight theorem must discharge the integral.
For `m=2p` and real alpha, identify the derivative with the real source moment.

### B. Exact cusp transformation

For

```text
tau = I * exp(I * alpha),
sigma = tau + 1,
tau' = -1 / sigma,
```

use `jacobiTheta₂_functional_equation`, theta translation, evenness, and quasi-periodicity to
rewrite Hardy's theta term as a principal square-root multiplier times the half-integer theta
series at `tau'`.

Every branch and multiplier must be checked with Mathlib's `Complex.cpow`; no informal square-root
choice is permitted.

### C. All-order tangential flatness

Along real `alpha -> pi/2` from below, prove the exact transformed geometry and a summable Gaussian
majorant for every polynomially weighted half-integer theta series. Show that its exponential
decay in `Im(tau')` absorbs every derivative and square-root loss. Deduce that every fixed
iterated derivative of `hardyThetaBoundaryTerm` tends to zero.

### D. Equation (3) and the Abel law

Differentiate the compiled equation (2), use the exact cosine derivative
`(-1)^p / 4^(2p)`, apply the theta flatness theorem, and obtain

```text
hardyXiAbelMoment alpha p
  -> (-1)^p * pi * cos(pi/8) / 4^(2p)
```

in the left-neighborhood filter. Combine this with interior integrability to construct
`HardyXiAbelMomentLaw`.

### E. Historical endpoint

Compose with `infinite_criticalLineZeros_of_hardyXiAbelMomentLaw`.

## Full-success criteria

`FULL_SUCCESS / HARDY_1914_UNCONDITIONAL_INFINITY_FORMALIZED` requires:

1. all-order actual integral differentiation for every `p`;
2. exact branch-aligned theta cusp transformation;
3. all-order tangential theta flatness;
4. the literal equation (3) moment limit with the source sign and `4^(2p)` constant;
5. `hardyXiAbelMomentLaw_unconditional : HardyXiAbelMomentLaw`;
6. infinitely many actual critical-line nontrivial zeros with no extra premise;
7. exact TargetChecks for the law and endpoint;
8. selected axiom prints showing only the accepted Lean/mathlib trust base;
9. warning-as-error compiles, forbidden scans, `git diff --check`, full build, frozen
   implementation, and public CI.

## Meaningful partial

`MEANINGFUL_CUSP_PARTIAL` requires both the exact modular cusp transformation and either:

- a proved all-order Gaussian flatness theorem with only the final derivative-identification API
  unresolved; or
- the complete actual integral differentiation plus a precisely isolated branch or uniform
  majorant obstruction on the transformed theta side.

Proving only `p=0`, only interior integrability, another conditional consumer, or a generic theta
identity without the Hardy path is not a meaningful partial.

## Falsification and negative controls

The campaign must stop or narrow if:

- the source and project theta normalizations differ by a translation, nome, or multiplier;
- `tau'` fails to remain in the upper half-plane on the real source path;
- the principal `cpow` multiplier does not match the half-integer theta identity;
- a derivative produces an exponential loss not absorbed by the transformed Gaussian;
- the actual integral derivative differs from `t^(2p)` by a sign or complex factor;
- the endpoint constant differs from `(-1)^p*pi*cos(pi/8)/4^(2p)`;
- the proof needs unconditional boundary integrability or totalized values at the cusp.

Mandatory controls:

- no use of `HardyXiAbelMomentLaw` in its own construction;
- no direct evaluation of `jacobiTheta` on the real boundary;
- no replacement of the left Abel filter by an ordinary endpoint integral;
- no custom Bohr--Riesz, Cesaro, Poisson, or theta-flatness axiom;
- no numerical limit as proof evidence.

## DAG and claim boundary

Before:

```text
Hardy equation (2)
  -> open equation (3) differentiation and tangential theta limit
  -> assumed HardyXiAbelMomentLaw
  -> compiled infinitely many critical-line zeros.
```

After full success:

```text
Hardy equation (2)
  -> compiled HardyXiAbelMomentLaw
  -> compiled infinitely many critical-line zeros.
```

This is a known 1914 theorem formalization. It does not prove a quantitative critical-line count,
a positive proportion of all zeros, H1, or RH. Its RH-frontier delta is zero even on full
success.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota; serving budget not exposed.
- `compaction_state`: inherited summary was followed by canonical-file reinspection; this
  preregistration is based on current repository state and a direct source-facsimile check.
- `global_goal`: active.
- `protected_files`: the six inherited modified/untracked files remain untouched and unstaged.

## Publication gate

Commit and push this docs-only preregistration first. Public Lean Action CI must pass before
editing any `LeanLab/` proof source, target registry, exact check, axiom audit, or root import.
