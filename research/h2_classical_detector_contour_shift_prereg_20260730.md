# H2 Classical Detector Contour-Shift Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Node: `H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_CI_PENDING`

## Parent and available chain

- `parent_closure`: H1 eta-to-Theta Abel-transfer receipt
  `524903f18b58322629f38ca7371920adf8d10765`, public run `30480635103`, build job
  `90673552785`, passed in `1m33s`.
- `available_modules`:
  `LeanLab/Riemann/ClassicalZeroDetectorMellin.lean`,
  `LeanLab/Riemann/ClassicalZeroDetectorInverseMellin.lean`,
  `LeanLab/Riemann/WeilZeroCutoff.lean`,
  `LeanLab/Riemann/BettinGonekInverseMellinConvolution.lean`,
  `LeanLab/Riemann/ReciprocalZetaSubpower.lean`, and
  `LeanLab/Riemann/BaezDuarteZetaRatio.lean`.
- `available_chain`: exact truncated-Mobius coefficient gap; actual mollifier--zeta product;
  forward Mellin transform; Gamma-pole cancellation at an actual zero; translated-zeta local
  residue; inverse Mellin identity on every source-valid positive line; rectangle boundary
  calculus; positive-strip Gamma-ratio control; and polynomial zeta growth on
  `1/2 <= Re(s) <= 8`.
- `first_open_obstacle`: `OBS-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`.

## Source statement

Let `rho` be an actual nontrivial zeta zero and put

```text
l = 1/2 - Re(rho),  w0 = 1-rho.
```

For `Y>0`, shift the actual inverse-Mellin factor

```text
Y^w * Gamma(w) * classicalDetectorMollifier M (rho+w) * zeta(rho+w)
```

from `Re(w)=2` to `Re(w)=l`. Prove that the only retained residue is

```text
Y^(1-rho) * Gamma(1-rho) * classicalDetectorMollifier M 1,
```

and derive

```text
classicalDetectorMellinLineIntegral M rho Y 2
  =
    Y^(1-rho) * Gamma(1-rho) * classicalDetectorMollifier M 1
    + classicalDetectorMellinLineIntegral M rho Y l.
```

Composing with the compiled inverse-Mellin theorem must give the corresponding formula for
`classicalDetectorSmoothedSeries M Y rho`.

## Fixed singularity model

The implementation must define a source-aligned holomorphic numerator of the form

```text
P(w) =
  Y^w
  * classicalDetectorMollifier M (rho+w)
  * Gamma(w+1)
  * dslope zetaPoleRemoved rho (rho+w).
```

For `w != 0` and `w != 1-rho`, it must prove

```text
P(w) / (w-(1-rho))
  =
  Y^w * Gamma(w) * classicalDetectorMollifier M (rho+w) * zeta(rho+w).
```

This simultaneously records the two different singularity decisions:

- `w=0` is removable because `zeta(rho)=0`;
- `w=1-rho` is retained because `zetaPoleRemoved 1=1`.

The residue evaluation must be an equality theorem, not only a punctured-neighborhood limit.
No simple-zero assumption on `rho` is allowed.

## Full-success criteria

`FULL_SUCCESS` requires all of the following:

1. Prove the numerator is differentiable on the half-plane needed by the closed rectangle,
   using the actual `zetaPoleRemoved`, finite mollifier, complex power, and shifted Gamma.
2. Prove the exact source equality away from `0` and `1-rho`, and evaluate
   `P(1-rho)` as the displayed source residue.
3. Prove a uniform fixed-strip majorant for the actual contour factor. It must combine finite
   mollifier control, positive-base complex-power control, zeta strip growth, Gamma recurrence,
   positive-strip Gamma ratios, and the exact half-line Gamma decay.
4. Prove both horizontal interval integrals tend to zero as the rectangle height tends to
   infinity.
5. Prove integrability of the actual contour factor on `Re(w)=2` and on
   `Re(w)=1/2-Re(rho)`.
6. Prove the finite rectangle identity with exactly one retained weighted Cauchy pole, then
   pass to the infinite line identity with the correct orientation and `2*pi*i`
   normalization.
7. Compose with `classicalDetectorInverseMellinLine` at `c=2` and prove the shifted
   smoothed-series identity.
8. Expose the coefficient-gap head/tail identity that precedes the source dyadic split. It
   may not claim the later Type-I/Type-II estimate without its actual block and tail bounds.
9. Register the existing Target
   `H2.classical-detector.inverse-mellin-contour-shift` as proven, with an exact TargetCheck,
   selected axiom prints, and the root import.

## Partial, falsification, and blocked criteria

`MEANINGFUL_PARTIAL` requires a compiled finite weighted-Cauchy rectangle identity for the
actual numerator and at least one actual horizontal-edge or shifted-line integrability theorem,
with the first failed analytic estimate stated exactly.

`FALSIFIED_STATEMENT` requires a compiled contradiction to the displayed contour identity under
the exact hypotheses `IsNontrivialZero rho` and `0<Y`, or a compiled normalization mismatch
showing that the stated residue or orientation is false.

`BLOCKED_API` requires the exact mathematical majorant and convergence theorem to be reduced to
one named unavailable library interface. Tactic friction or an unproved source estimate is not
an API block.

## Negative controls and claim boundary

- A local residue theorem is not an infinite contour shift.
- `VerticalIntegrable Gamma c` does not imply integrability after multiplication by a growing
  zeta factor on the shifted line.
- Pointwise horizontal decay is not enough; the whole finite-width horizontal integral must
  tend to zero.
- The left line satisfies `-1/2 < l < 0`. Gamma recurrence must avoid the pole at `w=0`;
  totalized division may not hide it.
- The contour crosses exactly `w=1-rho`; `w=0` must not be counted as a residue.
- No simplicity assumption on zeta zeros is permitted.
- No dyadic detector inequality, zero-density theorem, critical-line proportion, H2, or RH may
  be inferred from the shifted identity alone.

## Audit gates

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

The docs-only production gate passed at commit
`c82a77039e939d904038de1c39625bef50ea9dd3`, Lean Action run `30482171994`, build job
`90678758000`, in `2m12s`.

All nine full-success criteria now compile in
`LeanLab/Riemann/ClassicalZeroDetectorContourShift.lean`. The implementation proves:

- the pole-removed numerator is differentiable on the required half-plane;
- equality with the actual source factor away from `0` and `1-rho`;
- the exact retained residue at `1-rho`, with no simple-zero assumption;
- a uniform fixed-strip majorant and both horizontal-edge limits;
- integrability on the source line and the actual shifted line;
- the finite one-pole rectangle and infinite shifted-line identity;
- the shifted smoothed-series identity and exact coefficient-gap head/tail identity.

The aggregate certificate is `classicalDetectorContourShift_endpoint`, and Target
`H2.classical-detector.inverse-mellin-contour-shift` is locally registered as proven.
Warning-as-error passes for the new module and all registrations. Seven selected axiom prints
use only `propext`, `Classical.choice`, and `Quot.sound`; forbidden/resource scans and
`git diff --check` are empty; the full project build succeeds with `8802/8802`.

Local classification:
`FULL_SUCCESS / KNOWN_CONTOUR_SHIFT_FORMALIZED`.
The strict successor remains the actual dyadic Type-I/Type-II block and tail estimates used to
derive a zero-density dichotomy. No density exponent, H2 theorem, or RH is claimed.

Frozen implementation commit `b87e9164395b14723f61d8451e3ed1b0cd0ae1c8` passed Lean Action
run `30484701769`, build job `90687338466`, in `2m39s`. The five proof and registration files
have an empty diff from that commit. Immutable evidence is published separately and must pass a
fresh public run before the final ledger.

Immutable-evidence commit `1cc20bca2455d9eb9ca27a0e42fbaf86b340b4e8` passed Lean Action
run `30485116278`, build job `90688732121`, in `1m36s`. The frozen diff remains empty. The
final ledger is the next public gate.

Final-ledger commit `8ab5c9f0fcf187a240ad3bb371e14f788e127997` passed Lean Action
run `30485360308`, build job `90689557179`, in `2m13s`. The frozen diff remains empty. One
closure-receipt CI remains required.
