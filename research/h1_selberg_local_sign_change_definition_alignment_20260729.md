# H1 Selberg Local Sign-Change Definition Alignment

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-SELBERG-LOCAL-SIGN-CHANGE-01`

Status: `M0_ALIGNED / LOCAL_AUDIT_GREEN`

## Critical-line coordinate

The production module uses the existing real function
`LeanLab.Riemann.hardyXi : Real -> Real`. It does not claim literal equality with any particular
textbook normalization of Hardy's `Z` function.

The only zero-detection bridge used is the compiled project theorem

```text
hardyXi_eq_zero_iff_isNontrivialZero :
  hardyXi t = 0 <->
    IsNontrivialZero (1 / 2 + t * I).
```

Thus every zero produced by this campaign is an actual nontrivial zeta zero at a project-defined
critical-line point.

## Root mollifier

For coefficients `coeff : Nat -> Complex` and cutoff `N`, the finite root mollifier is

```text
sum n in Icc 1 N, coeff n * (n : Complex) ^ (-s).
```

The sum starts at `1`, avoiding the totalized `0 ^ (-s)` term. Any taper or arithmetic weight is
absorbed into `coeff`; no specific asymptotic coefficient choice is asserted.

On the critical line the real multiplier is

```text
normSq (selbergRootMollifier coeff N (1 / 2 + t * I)).
```

It is nonnegative but may vanish. The mollified real coordinate is exactly

```text
hardyXi t * selbergRootSquare coeff N t.
```

## Detection semantics

A zero of the mollified product is not a zeta-zero certificate because the root mollifier can
vanish. The compiled route instead obtains one strict negative and one strict positive value of
the product. Nonnegativity of the square transports those strict signs to `hardyXi`; continuity
then produces an actual `hardyXi` zero strictly between them.

For a finite family, `SelbergStronglySeparated left right` means

```text
forall i j, i < j -> right i <= left j.
```

Each witness lies in the corresponding open interval. Strong ordering therefore makes the
selected ordinates injective even when the closed interval endpoints touch.

## Claim boundary

The compiled endpoint is a deterministic local producer conditional on a strict local integral
triangle gap. It contains no Selberg global moment asymptotic, no construction of many detected
intervals, no `T log T` zero count, and no positive-proportion conclusion. It proves neither H1
nor RH.
