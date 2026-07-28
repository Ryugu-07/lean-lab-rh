# H1 Hardy Theta-Inversion Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H1-HARDY-THETA-INVERSION-01`

Selected node: `H1-HARDY-THETA-INVERSION-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_PENDING`

## Parent and materially new angle

The immediate parent campaign
`LITERATURE-20260728-H9-FRANEL-RANK-MERTENS-01` is publicly closed at final-ledger commit
`c96b0df5e6aabc705c9deddbe86d9c367c8f8fe2`, run `30373106791`, job
`90321789406`, in `1m36s`.

The nearest H1 campaign,
`LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01`, is publicly closed at final-ledger commit
`72f13a727fd71604095c054cb0f0574436c9795a`. It proves Hardy's high-moment sign
contradiction and infinitely many actual critical-line zeros conditional on
`HardyXiAbelMomentLaw`.

This campaign does not add another conditional consumer. It attacks the first missing source
input by reconstructing Hardy's interior theta identity from the project's actual xi and
Mathlib's actual Hurwitz-theta functional-equation pair.

## Locked primary source

G. H. Hardy, "Sur les zeros de la fonction zeta(s) de Riemann," *Comptes rendus de
l'Academie des sciences* 158 (1914), 1012--1014.

- facsimile:
  <https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN>
- page 1012, Cahen's formula and equation (1);
- page 1013, equations (2)--(3) and the tangential theta limit;
- page 1014, equations (4)--(6).

Corrected transcriptions, checked against the facsimile:

- <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1014>
- <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1015>
- <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1016>

No secondary source may replace the normalization in equations (1)--(2).

## Source equation and exact normalization

Define, for complex `y` with positive real part,

```text
HardyTheta(y) = 1 + 2*sum_{n>=1} exp(-n^2*y).
```

Hardy's equation (1), after writing `x=y/pi`, is

```text
1 + x^(-1/2)
  - (2/pi) * integral_{t in R}
      x^(-1/4-it) * Xi(2t)/(1/4+4t^2) dt
= HardyTheta(pi*x).
```

For complex `alpha` in the connected strip

```text
|Re(alpha)| < pi/2,
```

set `x=exp(i*alpha)`. Splitting the full real integral using the evenness of `Xi` gives
Hardy's equation (2):

```text
HardyXiInteriorIntegral(alpha)
  = pi*cos(alpha/4)
    - (pi/2)*exp(i*alpha/4)*
        HardyTheta(pi*exp(i*alpha)),
```

where

```text
HardyXiInteriorIntegral(alpha)
  = integral_0^infinity
      (exp(alpha*t)+exp(-alpha*t))*Xi(2t)/(1/4+4*t^2) dt.
```

For real `alpha`, this is exactly the source integrand already used by
`hardyXiAbelMomentIntegrand alpha 0`.

## M0 definition alignment

1. Source `Xi(t)` is project `hardyXi t = riemannXi(1/2+i*t)`.
2. Source `Xi(2t)` remains `hardyXi (2*t)`.
3. `hardyXi (2*t)=8*deBruijnNewmanH 0 (4*t)` is already compiled.
4. `HurwitzZeta.hurwitzEvenFEPair 0` has
   `f(x)=Theta(pi*x)`, `f0=1`, weight `1/2`, epsilon `1`.
5. Its `f_modif` is the pole-subtracted source side
   `Theta(pi*x)-1-x^(-1/2)`, with both constant terms present.
6. Its entire Mellin transform satisfies
   `P.Lambda0(q)=2*completedRiemannZeta0(2*q)`.
7. On `q=1/4+i*t`, solving the project xi definition gives the exact denominator
   `1/4+4*t^2`; no asymptotic replacement is allowed.
8. Mathlib's `mellinInv_mellin_eq` applies only at positive real `x`. Values
   `x=exp(i*alpha)` for real nonzero `alpha` require analytic continuation.
9. For complex alpha,
   `Re(pi*exp(i*alpha))=pi*exp(-Im(alpha))*cos(Re(alpha))`, which is positive exactly on
   the registered strip.
10. The displayed theta series starts at `n=1`. Lean may index by `n+1`, but may not include a
    second constant term.

## Proposed Lean surface

The intended module is
`LeanLab/Riemann/HardyThetaInversion.lean`.

Names may change to local style. Equivalent formulas may rearrange scalar factors, but the
source objects, open strip, and exact constants may not weaken.

```lean
def hardyThetaSeries (y : Complex) : Complex :=
  1 + 2 * tsum (fun n : Nat =>
    Complex.exp (-((n + 1 : Nat) : Complex) ^ 2 * y))

def hardyAlphaStrip : Set Complex :=
  {alpha | |alpha.re| < Real.pi / 2}

def hardyXiInteriorIntegral (alpha : Complex) : Complex :=
  integral (volume.restrict (Set.Ioi 0)) fun t : Real =>
    (Complex.exp (alpha * t) + Complex.exp (-alpha * t)) *
      hardyXi (2 * t) / (1 / 4 + 4 * t ^ 2)

theorem verticalIntegrable_hardyCompletedMellin :
    Complex.VerticalIntegrable
      (mellin
        (HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.f)
      (1 / 4)

theorem hardyCahenMellinInversion
    {x : Real} (hx : 0 < x) :
    -- Exact equation (1), in the equivalent f_modif normalization.
    ...

theorem analyticOnNhd_hardyXiInteriorIntegral :
    AnalyticOnNhd Complex hardyXiInteriorIntegral hardyAlphaStrip

theorem analyticOnNhd_hardyThetaSide :
    AnalyticOnNhd Complex
      (fun alpha =>
        Real.pi * Complex.cos (alpha / 4) -
          (Real.pi / 2) * Complex.exp (Complex.I * alpha / 4) *
            hardyThetaSeries
              (Real.pi * Complex.exp (Complex.I * alpha)))
      hardyAlphaStrip

theorem hardyXiInteriorIntegral_eq_theta
    {alpha : Complex} (halpha : alpha in hardyAlphaStrip) :
    hardyXiInteriorIntegral alpha =
      Real.pi * Complex.cos (alpha / 4) -
        (Real.pi / 2) * Complex.exp (Complex.I * alpha / 4) *
          hardyThetaSeries
            (Real.pi * Complex.exp (Complex.I * alpha))

theorem hardyXiAbelMoment_zero_eq_theta
    {alpha : Real} (halpha : |alpha| < Real.pi / 2) :
    (hardyXiAbelMoment alpha 0 : Complex) =
      Real.pi * Complex.cos (alpha / 4) -
        (Real.pi / 2) * Complex.exp (Complex.I * alpha / 4) *
          hardyThetaSeries
            (Real.pi * Complex.exp (Complex.I * alpha))
```

The first theorem may use the literal `f_modif` field of
`(HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair`. The final certificate must expose a
source-readable equation (1) or (2), not only a generic `mellinInv` equality.

## Proof spine

### Attack A: critical-line vertical integrability

1. Use the already compiled theta-kernel integral to bound
   `hardyXi (2*t)` uniformly on the real line.
2. Solve
   `riemannXi(s)=s*(s-1)/2*completedRiemannZeta0(s)+1/2`
   on `s=1/2+2*i*t`.
3. Obtain a majorant `C/(1/4+4*t^2)` for the completed Mellin transform.
4. Prove the majorant integrable on the full real line and register
   `VerticalIntegrable`.

Fallback A may instead combine the compiled critical-line zeta convexity bound with an exact
Gamma decay bound. It must still prove the literal completed transform integrable.

### Attack B: positive-real Cahen--Mellin inversion

1. Apply `mellinInv_mellin_eq` to the exact strong functional-equation pair.
2. Prove continuity of the concrete `f_modif` at every `x>0`.
3. Rewrite the inverse Mellin integral into the actual
   `completedRiemannZeta0(1/2+2*i*t)` line.
4. Substitute the xi identity and simplify every scalar to equation (1).
5. Rewrite `f_modif x` as
   `HardyTheta(pi*x)-1-x^(-1/2)`.

### Attack C: strip analyticity and identity theorem

1. Prove local dominated integrability of the xi integral on
   `|Re(alpha)|<pi/2`. A compact substrip has exponential margin against the known xi decay.
2. Prove local uniform summability and analyticity of
   `HardyTheta(pi*exp(i*alpha))` from positivity of
   `Re(pi*exp(i*alpha))`.
3. Map the positive-real inversion identity to the imaginary alpha-axis
   `alpha=i*u`.
4. Prove the strip is open and preconnected.
5. Apply the complex identity theorem from the imaginary-axis accumulation set.
6. Specialize to real alpha and identify the existing Hardy Abel integrand at `p=0`.

Fallback C may first prove equality on a nontrivial open neighborhood of zero and then use
connected-strip analytic continuation. It may not assume equality on the real alpha-axis.

## Adversarial and falsification controls

- `ALPHA_ZERO`: the formula at `alpha=0` must agree with positive-real Mellin inversion at
  `x=1`.
- `ALPHA_EVEN`: the xi integral is even in alpha. The theta side must compile the same identity
  through the theta functional equation; a mismatch signals a normalization error.
- `CONJUGATION`: conjugating alpha must conjugate both sides.
- `OPEN_STRIP`: no theorem may substitute `alpha=+/-pi/2` into the displayed theta series.
- `LEFT_ABEL_ONLY`: the later boundary value remains a one-sided limit.
- `FMODIF_CONSTANTS`: dropping either `1` or `x^(-1/2)` is a falsification.
- `INDEX_ONE`: `hardyThetaSeries` contains the source constant once and positive squares once.
- `XI_SCALE`: `Xi(2t)` and denominator `1/4+4*t^2` may not be replaced by `Xi(t)` or
  `1/4+t^2`.
- `NO_CONDITIONAL_INPUT`: `HardyXiAbelMomentLaw`, Hardy's zero theorem, RH, or a zero table may
  not be used to prove the interior identity.
- `NO_ENDPOINT_DIFFERENTIATION`: termwise derivatives at `alpha=pi/2` are outside this campaign.

If the alpha-evenness test fails, classify whether the error is the theta modular factor,
Mellin sign, full-line split, or completed-zeta normalization before changing a statement.

## Success, meaningful partial, and local stop

`FULL_INTERIOR_THETA_IDENTITY_SUCCESS` requires:

- Attacks A--C;
- the source-readable complex strip identity and real-alpha equation (2);
- exact controls at alpha zero, evenness, and conjugation;
- one proven aggregate Target and exact TargetChecks;
- selected transitive axiom prints containing standard axioms only;
- empty forbidden/custom-declaration/resource-relaxation scans;
- warning-as-error module compilation, `git diff --check`, and full `lake build`;
- frozen implementation, immutable evidence, and final-ledger public CI.

`MEANINGFUL_MELLIN_INVERSION_PARTIAL` requires:

- Attack A and Attack B in the literal source normalization;
- a proven positive-real equation (1);
- the first failed theorem of Attack C recorded in theorem-shaped form;
- all mechanical and public gates.

`SOURCE_NORMALIZATION_CORRECTION` is recorded if the facsimile and project objects force a
different exact scalar or complex-conjugation convention. Both the original transcription and
corrected statement must be tested at alpha zero.

`FALSIFICATION` requires a compiled contradiction or concrete exact counterexample to a
source-aligned displayed identity after all M0 conventions are checked.

Local stop occurs at full success, meaningful partial, source correction, or falsification.
Local stop returns to fresh cross-family route selection; the global RH Goal remains active.

## Strict boundary

Even full success proves only Hardy equation (2) in the open strip. It does not by itself prove:

- all-order differentiation under the integral;
- the tangential Bohr--Riesz theta limit as `alpha -> pi/2` from the left;
- `HardyXiAbelMomentLaw`;
- Hardy's unconditional infinitude theorem in the current project;
- the Hardy--Littlewood linear lower count;
- a positive proportion of critical-line zeros;
- H1 or RH.

The next source edge after full success is the all-order derivative identity plus the tangential
theta derivative limit. It must be separately preregistered.

## Production and runtime gates

Before proof-source editing:

- publish this docs-only preregistration and route-selection record;
- require public Lean Action CI to pass;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register one aggregate Target in `Targets.lean`;
- add exact witnesses in `TargetChecks.lean`;
- print selected transitive axioms in `AxiomsAudit.lean`;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`, and relaxed
  resource options;
- compile with warnings as errors and run the full build;
- freeze proof sources before immutable evidence.

Runtime record:

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: continued from compacted H9 public closure; reread current governance,
  current historical ruling, live Targets, H1/H2/H7/H10/H12 route state, Hardy 1914 equations
  (1)--(6), the existing Hardy consumer, Mathlib Mellin inversion, and the existing H6
  theta/Mellin implementation before selection.
- `global_goal`: active.

