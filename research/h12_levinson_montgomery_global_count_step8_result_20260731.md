# H12 Levinson--Montgomery Global Count Steps 8-9 Result

Date: 2026-07-31

Campaign:
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`

Status: `STEP_8_FULL_SUCCESS / STEP_9_MEANINGFUL_PARTIAL /
IMMUTABLE_EVIDENCE_PUBLIC_GREEN / CLOSURE_LEDGER_CI_REQUIRED`

## Source recheck

The fixed primary source is Levinson and Montgomery, *Zeros of the derivatives of the Riemann
zeta-function*, Acta Mathematica 133 (1974), Theorem 1 and section 2:

`https://doi.org/10.1007/BF02392141`

Page 52 uses a closed contour with bottom `t=10`. Before the exact-count argument, the authors
invoke explicit zero-count estimates and low-zero verification to establish strict negativity of
`Re(zeta'/zeta)` at that base. The exact-count branch is therefore anchored by a finite low-height
datum; cofinal negative top heights alone determine only a constant count offset.

## Unconditional result

The new no-sorry module
`LeanLab/Riemann/LevinsonMontgomeryCriticalStrip.lean` proves

```lean
theorem levinsonMontgomeryLogCountBound_actual :
    LevinsonMontgomeryLogCountBound
```

This is the first conclusion of Levinson--Montgomery Theorem 1 for the project's actual
multiplicity-bearing counts and for every sufficiently large real cutoff.

The proof has four main parts.

1. Compactness of every critical-line height segment thickens the compiled punctured negative
   geometry into one uniform strict-left strip.
2. The finite divisor cutoff is chosen inside that strip. The same `r<1/2` therefore lies to the
   right of every strict-left divisor point and keeps `zeta'/zeta` strictly left-pointing on the
   whole right vertical side.
3. Along a vertical line,
   `I * integral(logDeriv zeta' - logDeriv zeta)` is the principal-log endpoint change of
   `-zeta'/zeta`. Its imaginary part is an argument variation bounded by `pi`, not a logarithmic
   modulus term. The fixed left side has the same bound.
4. The compiled Jensen top variations, a uniform fixed-bottom partial integral bound, and finite
   bad-height support yield an admissible `O(log(t+2))` estimate and then transfer both finite
   counts unchanged to every sufficiently large real `T`.

No low-zero table, CountDichotomy, Speiser zero-free premise, or RH is used in this theorem.

## Exact-count reduction

The module defines the finite predicates

```lean
def LevinsonMontgomeryNegativeExactCountBase : Prop :=
  exists b : Real, 10 < b and SpeiserStrictNegativeHorizontal b and
    speiserUpperLeftDerivZeroCount b = speiserUpperLeftZetaZeroCount b

def LevinsonMontgomeryHeightTenCertificate : Prop :=
  SpeiserStrictNegativeHorizontal 10 and
    speiserUpperLeftDerivZeroCount 10 = speiserUpperLeftZetaZeroCount 10
```

Lean then proves:

```lean
theorem levinsonMontgomeryExactCountSequence_of_negativeExactCountBase_of_cofinalGeometry
    (hbase : LevinsonMontgomeryNegativeExactCountBase)
    (hcofinal : LevinsonMontgomeryCofinalNegativeHeightGeometry) :
    LevinsonMontgomeryExactCountSequence

theorem levinsonMontgomeryCountDichotomy_of_negativeExactCountBase
    (hbase : LevinsonMontgomeryNegativeExactCountBase) :
    LevinsonMontgomeryCountDichotomy

theorem levinsonMontgomeryNegativeExactCountBase_of_heightTenCertificate
    (hcert : LevinsonMontgomeryHeightTenCertificate) :
    LevinsonMontgomeryNegativeExactCountBase

theorem levinsonMontgomeryTheoremOne_of_heightTenCertificate
    (hcert : LevinsonMontgomeryHeightTenCertificate) :
    LevinsonMontgomeryLogCountBound and LevinsonMontgomeryCountDichotomy
```

The exact winding proof uses the same adaptive straight contour as the count theorem. Principal
logarithms on the bottom, top, right, and left sides cancel endpoint by endpoint, so the rectangle
boundary difference is exactly zero. The global count identity then preserves the base count
offset. When that offset is zero, every cofinal selected height has equal counts.

Compactness propagates the height-ten strict sign to a small band above ten. Extensional equality
of the actual finite zeta and derivative zero sets proves that neither multiplicity-bearing count
changes in this band. Thus the `b>10` base used by the uniform-strip theorem is not an extra
historical assumption.

## Failed attacks and exact obstruction

Three materially different attacks were made on the second source conclusion.

1. Comparing two cofinal negative heights proves invariance of the count difference but leaves an
   arbitrary integer offset. The unconditional `O(log T)` estimate does not force a fixed offset
   to vanish.
2. Four-side principal-log cancellation closes all high-contour topology from one zero-offset
   base, exposing rather than eliminating the base dependency.
3. The primary source, pinned Mathlib, and project inventory were checked for a certified
   low-height theorem. The source invokes numerical low-zero information, while no local theorem
   proves the required actual zeta and zeta-derivative certificate.

The first unavailable theorem is now exactly

```lean
theorem levinsonMontgomeryHeightTenCertificate_actual :
    LevinsonMontgomeryHeightTenCertificate
```

It must be proved by a rigorous low-height zero analysis, an equivalent certified argument
principle computation, or a different theorem that fixes the count offset. Numerical tables by
themselves are navigation evidence and cannot be imported as a proof premise.

## Audit boundary

- `levinson_montgomery_log_count_bound_delta=1`;
- `adaptive_uniform_negative_strip_delta=1`;
- `four_side_zero_winding_delta=1`;
- `height_ten_dependency_isolation_delta=1`;
- `levinson_montgomery_count_dichotomy_delta=0`;
- `speiser_equivalence_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

The new module, aggregate import, Targets, TargetChecks, and AxiomsAudit pass warning-as-error.
Nine selected theorem prints use only `propext`, `Classical.choice`, and `Quot.sound`; the
campaign forbidden scan and `git diff --check` are empty; the full build passes `8819/8819` with
inherited warnings only. The full Theorem 1 conjunction, unconditional Speiser equivalence,
derivative-zero exclusion, and RH remain open. The persistent RH Goal remains active.

Frozen implementation commit `6863823d119977a660d0643595cbfc61b7282018` passed public Lean
Action run `30653076645`, build job `91230777600`, in `2m18s`. Immutable docs-only evidence is
recorded at commit `0e22bd751a4e51c16fef3015fb1361b76f865df0`; Lean Action run
`30653415405`, build job `91231875566`, passed in `2m5s` with all five frozen Lean blobs
unchanged. A docs-only local closure ledger remains required.
