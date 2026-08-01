# H14 x H12 Height-Ten Complete-Boundary Preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Primary mode: `PROOF-ATTEMPT / HISTORICAL-SOURCE-REENTRY`

Status: `PREREGISTERED / PRODUCTION_EDIT_PENDING_PUBLIC_CI / GLOBAL_GOAL_ACTIVE`

## Historical source signal

In the proof of Theorem 9, Levinson and Montgomery explicitly say that direct consideration of
`zeta'(it)` and `zeta(it)`, equivalently values at `1+it` through the functional equation, gives
an argument change of approximately `-2*pi` between `-6.254` and `6.254`. See page 53 of
[Zeros of the derivatives of the Riemann zeta-function](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf).

The project's left vertical edge `s=iy`, `0<=y<=10`, contains the positive half of precisely
this transition. The project already proves the source sign on the same axis for `y>=10`, so the
remaining interval is a genuine low-height source gap.

On the right vertical, the standard Hardy normalization makes
`exp(i*theta(t))*zeta(1/2+it)` real. The corresponding theta function is built from
`Gamma(1/4+it/2)` and `log pi`; see [DLMF 25.10.1--25.10.2](https://dlmf.nist.gov/25.10).
This identifies the same Gamma transition as a structural input rather than a numerical
coincidence.

## Route selection

Let `q(s)=zeta'(s)/zeta(s)`. Membership of `I*q(s)` in `Complex.slitPlane` fails exactly when
`q(s)` lies on the positive imaginary ray. A navigation-only high-precision grid suggests the
same rational three-zone avoidance certificate on both vertical edges:

1. `Re q(s)>0` for `0<=y<=6`;
2. `Im q(s)<0` for `6<=y<=13/2`;
3. `Re q(s)<0` for `13/2<=y<=10`.

The complete top edge at height ten navigates with `Re q(s)<0`. These observations select the
attack but are not theorem premises.

Select the complete remaining boundary rather than a separate optimization of either crossing
location. Full success is the literal height-ten certificate.

## Exact mathematical targets

For `sigma=0` and `sigma=1/2`, prove all three actual quotient signs

```text
0 <= y <= 6       -> Re q(sigma+iy) > 0
6 <= y <= 13/2    -> Im q(sigma+iy) < 0
13/2 <= y <= 10   -> Re q(sigma+iy) < 0.
```

Use these signs to prove both clauses of
`SpeiserPositiveImaginaryRayVerticalBoundary 10`.

Independently prove `SpeiserStrictNegativeHorizontal 10` on the complete top segment
`0<=sigma<=1/2`. Compose the already compiled boundary constructor to obtain

```lean
theorem speiserPositiveImaginaryRayVerticalBoundary_heightTen :
    SpeiserPositiveImaginaryRayVerticalBoundary 10

theorem speiserStrictNegativeHorizontal_heightTen :
    SpeiserStrictNegativeHorizontal 10

theorem speiserRotatedSlitBoundary_heightTen :
    SpeiserRotatedSlitBoundary Complex.I 10

theorem levinsonMontgomeryHeightTenCertificate_actual :
    LevinsonMontgomeryHeightTenCertificate
```

Names may change only for elaboration or namespace reasons; statements may not be weakened.

## Planned proof architecture

1. Prove the critical-line completion identity needed to express the real part of `q` through
   the actual Gamma logarithmic derivative wherever zeta is nonzero.
2. Re-enter the Levinson--Montgomery imaginary-axis functional-equation calculation and expose
   an exact finite evaluator at the reflected points `1-iy`.
3. Derive explicit uniform value and derivative bounds on complex neighborhoods of the three
   rational zones. Add a second-derivative or Cauchy variation bound only where point balls do not
   already certify a complete interval.
4. Kernel-check rational centers and radii. Every finite center must reduce to exact Lean
   arithmetic plus proved transcendental enclosures.
5. Prove the six vertical signs and the complete top sign from those enclosures, then invoke the
   existing rotated-slit and height-ten constructors.

The proof may use a different finite cover or stronger structural sign if Lean exposes one. It
may not replace any actual-function target by a finite-center proxy.

## Success criteria

Full subattack success requires all of the following:

- actual zeta and derivative data, not sampled or imported booleans;
- all three zones on both vertical edges;
- actual nonvanishing wherever division is used;
- the complete `SpeiserStrictNegativeHorizontal 10` target;
- `SpeiserRotatedSlitBoundary I 10`;
- the literal `LevinsonMontgomeryHeightTenCertificate`;
- exact TargetChecks and standard-only axiom prints;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed resource
  option.

An abstract three-zone implication, a certificate at finitely many points without proved
coverage, or a theorem conditional on an external zero table is not full success.

## Falsification and stopping criteria

- If any proposed zone sign is false, record the first rigorous counterexample or the exact
  failing enclosure and repartition by a rational endpoint. Do not optimize the crossing value.
- If the Hardy/Gamma identity leaves a zero-dependent term on the critical line, preserve the
  exact identity and move that zone to direct actual-zeta evaluation.
- If the left functional-equation transfer is singular at `y=0`, use the compiled real-bottom
  endpoint theorem and cover only `0<y<=10` by reflection.
- If a uniform variation bound forces an impractical cover, compare a direct interval extension
  of the Euler--Maclaurin finite formula with a higher-order Cauchy bound; record the precise
  derivative bottleneck before changing methods.
- Stop this local subattack only after the literal certificate is proved, a candidate sign is
  rigorously falsified, or the chosen evaluator is proved inadequate and its exact obstruction is
  logged. A local stop never pauses the parent campaign or global RH Goal.

## Assumption and claim boundary

The implementation may reuse only compiled project theorems and standard Mathlib declarations.
Navigation decimals, `mpmath`, Platt--Trudgian computations, and the approximate `6.254` source
value are not premises.

The expected selected axiom frontier is only `propext`, `Classical.choice`, and `Quot.sound`.

Even full success closes a fixed low-height source datum; it does not by itself prove
CountDichotomy, Speiser equivalence, H12, or RH unless those exact downstream declarations also
compile without additional open hypotheses.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from the active Goal summary; governance, protected-file rules,
  current attempts, hard-gap DAG, source modules, completed bottom producer, critical-line sign
  modules, Gamma/digamma modules, and original-source pages were re-read before selection.
- `global_goal`: active.
