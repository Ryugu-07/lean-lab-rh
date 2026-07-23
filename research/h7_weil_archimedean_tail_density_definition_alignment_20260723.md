# H7 Weil Archimedean Tail Density Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H7-WEIL-ARCHIMEDEAN-TAIL-DENSITY-01`

Status: `LOCALLY_PROVEN / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Source objects

The module uses the literal source quantities

```text
h_+(r) = Re digamma(1/4+i*r/2) - log pi,
rho = 2*pi/L,
S(r,x,L) = integral_0^L sin(2*pi*x*(1-y/L))*cos(r*y) dy.
```

`weilArchimedeanTailSource` is exactly `(1/pi^2)h_+(r)S(r,x,L)`. Its derivative sample is defined
from the differentiated interval integrand, not from an integer-node surrogate.

## Compiled identities

For integer `n`, `a=r/rho`, and nonvanishing band denominators, Lean proves

```text
S(r,n,L) = (2*sin(L*r/2)^2/rho) * n/(a^2-n^2),

partial_x S(r,x,L)|_(x=n)
  = (2*sin(L*r/2)^2/rho) * (a^2+n^2)/(a^2-n^2)^2.
```

The finite divided-difference matrix built from the actual value and derivative samples is

```text
h_+(r)*sin(L*r/2)^2/(pi^2*rho) * (p_r*p_r^t + q_r*q_r^t),
p_r(n)=1/(a-n), q_r(n)=1/(a+n).
```

Its quadratic form is the same scalar times the sum of the two squared dot products. Reflection
exchanges `p_r` and `q_r`, so the actual density matrix preserves the even and odd sectors.

## Analytic infrastructure

Mathlib did not expose a ready-made continuity theorem for `digamma`. The implementation proves
Gamma is analytic on the right half-plane from its compiled differentiability there, applies
analyticity of the derivative and Gamma nonvanishing, and obtains continuity of `digamma=Gamma'/Gamma`
along `1/4+i*r/2`. This proves interval integrability of every finite matrix entry without a new
axiom or an extra campaign premise.

## Integrated result

`weilFiniteArchimedeanIncrement` is the entrywise interval integral of the actual density
matrices. Its finite quadratic contraction equals the interval integral of the pointwise
two-square density. Under the explicit premise `0<=h_+(r)` throughout the interval, the increment
is positive semidefinite.

This is conditional semidefiniteness. The source's unconditional `h_+(r)>0` threshold, strict
positive definiteness, total positivity, infinite tail limit, total Weil matrix sign, Herglotz
inequality, simple-even theorem, source convergence, H7, and RH are not proved.

## Mechanical audit

- New module: 973 lines, direct warning-as-error compile passed.
- Exact TargetChecks: 12.
- Selected axiom prints: 11, all standard-only (`propext`, `Classical.choice`, `Quot.sound`).
- Forbidden-token and resource-relaxation scan: empty.
- `git diff --check`: passed.
- Full local build: `8756/8756` jobs passed; replay warnings are inherited from existing files.
