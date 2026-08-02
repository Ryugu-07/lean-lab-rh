# Height-ten left boundary above seven checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Active subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Status: `LOCAL_SUCCESS / PUBLIC_IMPLEMENTATION_PENDING / COMPLETE_BOUNDARY_ACTIVE /
GLOBAL_GOAL_ACTIVE`

## Route decision

The attempted shortcut was to combine structural nonvanishing of `zeta(iy)` with negativity of
the imaginary-axis Levinson--Montgomery archimedean term on the full preregistered high zone
`13/2<=y<=10`.

Navigation-only high precision evaluates that term as positive at `y=13/2` and places its sign
change strictly between `13/2` and `7`. This is not a Lean theorem or a premise. It rejects only
the Gamma-only mechanism for the full interval; it does not reject the actual quotient sign,
because Equation (2.1) retains a nonpositive paired-zero contribution on the imaginary axis.

The selected exact subinterval is therefore `y>=7`. The residual `[13/2,7]` is reserved for a
paired-zero lower-mass argument or proof-producing direct actual-zeta evaluation.

## Compiled outputs

The new module `LevinsonMontgomeryHeightTenLeftHigh.lean` proves:

```text
0<y -> riemannZeta(iy) != 0;
7<=y -> levinsonMontgomeryLogDerivArchimedeanTerm(iy) < 0;
7<=y -> Re(speiserZetaDerivRatio(iy)) < 0;
7<=y -> I*speiserZetaDerivRatio(iy) belongs to Complex.slitPlane.
```

The first theorem is structural. A hypothetical xi zero at real part zero contradicts the
compiled positivity of the real part of every nontrivial zero. The nonpole xi factorization then
forces zeta nonvanishing.

For the second theorem, one digamma shift moves `1+iy/2` to `2+iy/2`. At `y>=7`, exact norm-square
bounds, the existing proof-producing logarithm enclosure, and the compiled Stirling remainder
give a strict rational negative margin. Equation (2.1) and the nonpositive paired-zero sum transfer
this to the actual quotient.

## Verification

- The production module, project entry, Targets, TargetChecks, and AxiomsAudit pass
  `-DwarningAsError=true`.
- The four selected final declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused `sorry`, `admit`, `native_decide`, custom-axiom, `opaque`, `unsafe`, and resource-option
  scans are clean.
- `git diff --check` is clean.
- Full local build passes `8835/8835`.

## Strict boundary

This checkpoint closes only the left vertical boundary for `7<=y<=10` within the height-ten
rectangle. It does not close `[13/2,7]`, the left low/middle zones, the right low/middle zones, the
compact-middle top interval, the complete rotated-slit boundary, the height-ten certificate, H12,
or RH.

The complete-boundary subattack, parent campaign, and global RH Goal remain active.
