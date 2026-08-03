# H12 Height-Ten Left Middle Cell Receipt

Date: 2026-08-03

Implementation: `a4ded06a39519fa1c37d0e97aef8e60a32eb33fb`

Implementation CI: run `30819281694`, build job `91704779376`, passed in `3m51s`.

Immutable evidence: `b084ee0599599dd16c278669071adca4465b9016`

Evidence CI: run `30819751545`, build job `91706377959`, passed in `2m42s`.

All five frozen Lean blobs match across both commits.

The compiled result proves the actual strict phase sign

```text
Im(zeta'(iy)/zeta(iy)) < 0 for every 6<=y<=13/2.
```

The proof uses a single exact rational `N=4` cell, full complex phase transport, componentwise
Bernstein certificates, an exact shifted archimedean argument decomposition, and an
actual-function quotient ball. No external zero table, sampled premise, custom axiom,
placeholder, unsafe declaration, opaque declaration, or resource relaxation is used.

This closes the left middle-cell subattack at the preregistered `meaningful_partial` threshold.
It does not close positive real part on `(0,6]`, the complete left edge, any other height-ten
boundary producer, the complete height-ten certificate, H12, or RH. The enclosing phase
campaign, parent complete-boundary campaign, and global RH Goal remain active.
