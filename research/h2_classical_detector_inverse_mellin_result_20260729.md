# H2 Classical Detector Inverse Mellin Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-01`

Node: `H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-LINE-01`

Classification: `FULL_SUCCESS / KNOWN_INVERSE_MELLIN_EDGE_FORMALIZED`

Public state: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

## Compiled result

The new module `LeanLab/Riemann/ClassicalZeroDetectorInverseMellin.lean` proves:

1. `verticalIntegrable_Gamma_of_pos`: `Gamma` is integrable on every vertical line
   `Re(w)=c` with `c>0`.
2. `exp_eq_inverseMellin_Gamma`: for every `x>0` and `c>0`,

   ```text
   exp(-x) = (1/(2*pi)) * integral_t x^(-(c+t*i)) Gamma(c+t*i).
   ```

3. Every actual detector line term is Bochner integrable.
4. The sum of its integral norms is summable whenever `Re(z)+c>1`.
5. The pointwise term sum is exactly the production
   `classicalDetectorMellinContourFactor`, including the actual truncated-Mobius
   L-series, mollifier, and Riemann zeta.
6. `classicalDetectorInverseMellinLine : ClassicalDetectorInverseMellinLine`.

The proven Target is `H2.classical-detector.inverse-mellin-line`.

## Proof mechanism

The arbitrary-line Gamma theorem is not assumed. Lean starts from the exact identity

```text
norm(Gamma(1/2+i*t))^2 = pi/cosh(pi*t)
```

and derives exponential decay on the half line. The existing fixed-positive-strip Gamma-ratio
theorem introduces only a real-power loss, which the exponential decay absorbs into an
integrable `|t|^-2` majorant. Lines below `1/2` are reduced to lines above `1/2` by the Gamma
recurrence.

Mathlib's Fourier-derived `mellinInv_mellin_eq` is then specialized to `x -> exp(-x)`. The final
detector exchange uses the actual absolute L-series summability at `Re(z)+c>1`; no analytic
continuation or assumed contour theorem is inserted.

## Omission reading

The named inverse-line gap was a formalization omission, not a mathematical obstruction. Modern
Mellin inversion plus estimates already present in the project close it exactly. The historical
route is now shorter:

```text
compiled inverse Mellin line
  -> infinite rectangle shift to Re(w)=1/2-Re(rho)
  -> horizontal-edge decay for Gamma*mollifier*zeta
  -> shifted detector and dyadic blocks
  -> Type-I/Type-II or large-value production
  -> zero-density consequences.
```

This is useful route progress but does not move the RH frontier by itself.

## Audit

- production module: 702 lines;
- exact TargetChecks: three new checks;
- selected axiom prints: three, each only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, custom axiom, `native_decide`, `opaque`, or `unsafe`;
- no heartbeat, recursion-depth, or resource relaxation;
- warning-as-error compiles: pass for the module, Targets, TargetChecks, AxiomsAudit, and root;
- full project build: `8794/8794`;
- protected inherited files remain untouched and unstaged.

## Claim boundary

This result does not shift the contour, prove either horizontal edge tends to zero, derive the
shifted detector identity, prove a density estimate, exclude sparse off-line zero patterns, prove
H2, or prove RH.

Deltas: historical route coverage `+1`, source analytic bridge `+1`, hard gap `0`, RH frontier
`0`.

The persistent RH Goal remains active. The implementation must pass public CI before immutable
evidence or final closure is recorded.

## Public implementation evidence

Frozen implementation commit `8c5d820a92178dfd3ad3582e9ffe733a7377bb0e` passed public Lean
Action run `30414837829`, build job `90458965005`, in `2m59s`.

The frozen proof and registration set is:

- `LeanLab/Riemann/ClassicalZeroDetectorInverseMellin.lean`;
- `LeanLab/Riemann/Targets.lean`;
- `LeanLab/Riemann/TargetChecks.lean`;
- `LeanLab/Riemann/AxiomsAudit.lean`;
- `LeanLab.lean`.

The immutable-evidence, final-ledger, and closure commits must leave this set unchanged from the
frozen implementation.
