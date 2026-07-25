# H7 Weil Finite Dictionary Admissibility Definition Alignment

Date: 2026-07-24

Campaign: `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-ADMISSIBILITY-01`

Primary source: Groskin, arXiv:2607.02828, Lemma 2.2 and the definitions immediately preceding it.

Lean source: `LeanLab/Riemann/WeilFiniteDictionaryAdmissibility.lean`

## Source-to-Lean map

| source object or property | Lean declaration | alignment |
| --- | --- | --- |
| `K_u(0)=0` | `weilFiniteVolterraKernel_zero` | derived from the literal oriented Volterra integral |
| `Delta=log(C)/(2*pi)` | `weilFiniteDictionaryBandwidth C` | reused from the source-calculus module |
| compact Fourier weight `hat(g_u)` | `weilFiniteDictionaryFourierWeight C N u` | exactly `pi*K_u(1-|xi|/Delta)` in the band and zero outside |
| source test `g_u(z)` | `weilFiniteDictionaryTest C N u z` | exact integral over `[-Delta,Delta]` with phase `exp(2*pi*i*z*xi)` |
| logarithmic physical density | `weilFiniteDictionaryPhysicalDensity C N u` | exactly `(1/(2*pi))*exp(-x/2)*hat(g_u)(x/(2*pi))` |
| project Laplace coordinate | `weilFiniteDictionaryTest_zeroCoordinate` | `g_u((s-1/2)/i)=compactLaplaceTransform f_u s` |
| project symmetric zero weight | `weilFiniteDictionaryTest_xiDivisorZero` | exact equality at every multiplicity-bearing xi divisor index |
| horizontal-strip decay | `norm_weilFiniteDictionaryTest_le_stripDecay` | explicit nonnegative strip constant and inverse-square decay |
| absolute xi-zero summability | `summable_norm_weilFiniteDictionaryTest_xiDivisorZero` | actual divisor index, including analytic multiplicity |

## Boundary and regularity checks

- The Fourier weight is represented by a continuous clamped chord. This proves continuity at
  `xi=0` and both band endpoints, exact support in `[-Delta,Delta]`, and integrability.
- The physical density is continuous and compactly supported after the exact logarithmic
  coordinate change.
- The entire test is proved complex differentiable everywhere from the compact integral. Its
  evenness is obtained by the substitution `xi -> -xi`.
- The exponential-type estimate has literal width
  `2*pi*Delta=log(C)`; no larger surrogate bandwidth is used.
- The weight need not be globally `C^1`. Lean splits it into smooth left and right branches,
  integrates by parts twice on each half, cancels only the value boundaries, and retains all
  derivative-jump and second-derivative terms.
- This smooth-half decomposition proves the source inverse-square decay without assuming a
  nonexistent global `C^2` fact and without requiring a new Stieltjes integration API.
- At `z=(rho-1/2)/i`, Lean proves `Re(z)=Im(rho)` and `Im(z)=1/2-Re(rho)`. The critical-strip
  bounds put every actual xi zero in the strip `|Im(z)|<=1/2`.
- The comparison
  `(1+|Im(rho)|)^-2 <= norm(rho)^-2` and the existing Hadamard reciprocal-square theorem give
  absolute summability. No RH, zero simplicity, zero ordering, or local zero-count asymptotic is
  assumed.

## Result and boundary

`weilFiniteDictionaryAdmissibility_endpoint` packages the source boundary regularity,
entire/even and exponential-type properties, exact project coordinates, horizontal-strip decay,
and both norm and value summability over the actual xi divisor. The alignment probe found no
sign, `2*pi`, `1/2`-shift, support, or multiplicity mismatch.

This endpoint does not prove a Guinand--Weil arithmetic explicit formula for the weaker
continuous piecewise-smooth class. It does not identify the total finite matrix quadratic with
the zero sum, transport the pole or archimedean blocks, prove pole-neutral survival,
inverse/density, cutoff convergence, positivity, H7, or RH.

## Local audit

The 1,819-line source and all three governance modules compile directly with warnings treated as
errors. The selected transitive axiom sets contain only `propext`, `Classical.choice`, and
`Quot.sound`; the production forbidden scan and `git diff --check` are empty, and the full
`8759/8759` build passes.

## Public freeze

Frozen implementation commit `257b80dcda7d4a68a9c6a4b9860b1a97fa42c0ca` passed public Lean
Action run `30140659408`, build job `89633127915`, in `2m37s`. All proof and governance source is
frozen at this coordinate. Docs-only immutable-evidence commit
`317a610f22637fd91ae84f125b3086f552081813` passed run `30140782861`, build job
`89633473809`, in `1m32s`; final-ledger CI remains.
