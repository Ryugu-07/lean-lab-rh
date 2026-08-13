# H12 Height-Ten Left Low Pole-Cancelled Receipt

Date: 2026-08-13

Preregistration: `fe81ed5c57d37829ed07994426b8c1c5f66a6a34`

Preregistration CI: run `31664365098`, build job `94335663536`, passed.

Implementation: `69eb02d96f64ba3e94794c7b8f79f9d2f2171834`

Implementation CI: run `31666657844`, build job `94342566271`, passed in `2m46s`.

Immutable evidence: `5c1869fa413e7af67a33a45a06adbac3840cf8e5`

Evidence CI: run `31666841899`, build job `94343181130`, passed in `2m7s`.

All five frozen Lean blobs match across the implementation and evidence commits.

The compiled result proves the actual strict phase sign

```text
Re(zeta'(iy)/zeta(iy)) > 0 for every 0<=y<=1/4.
```

The proof removes the reflected zeta pole before error transport, simplifies the `N=1` finite
centers to exact rational polynomials, and verifies strict center, denominator, and error margins
for the full interval. The exact zero endpoint is separated from the positive-height finite
quotient, avoiding the junk value introduced by totalized complex division. No external zero
table, sampled premise, custom axiom, placeholder, unsafe declaration, opaque declaration, or
resource relaxation is used.

This closes the pole-cancelled low-cell subattack at the preregistered `full_success` threshold.
It does not close positive real part on `[1/4,6]`, the complete left edge, other height-ten
boundary producers, the complete height-ten certificate, H12, or RH. The enclosing phase
campaign, parent complete-boundary campaign, and global RH Goal remain active.
