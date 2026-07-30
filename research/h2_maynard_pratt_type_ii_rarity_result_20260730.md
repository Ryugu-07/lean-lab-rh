# H2 Maynard--Pratt Type-II Rarity Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Node: `H2-MAYNARD-PRATT-TYPE-II-RARITY-01`

Classification:
`HARD_GAP_REDUCED / CONDITIONAL_REDUCTION_PUBLIC_GREEN / SOURCE_DISPLAY_FALSIFIED_AND_REPAIRED`

Local campaign status: `PARKED_AT_EXACT_ANALYTIC_PRODUCER`

Global RH Goal status: `ACTIVE`

## Fixed endpoint

The campaign reconstructed Maynard--Pratt, Appendix C, Lemma 24 for the project's actual
Type-II shifted integral and literal source mollifier. Full success required the unconditional
multiplicity-bearing estimate

```text
R_II(sigma,T) <= C * T^(2*(1-sigma)) * (log T)^A.
```

The campaign reached a public-green theorem conditional only on the specific short-Mobius
twisted fourth moment. It did not prove that moment or the displayed rarity bound.

## Compiled chain

The public implementation contains:

1. `MaynardPrattTypeIIRarity.lean`
   - the actual multiplicity-bearing Type-II count;
   - the literal source mollifier--zeta value on the critical line;
   - the exact shifted-integrand norm identity;
   - the corrected Gamma recurrence bound and uniform source tail;
   - the unconditional local fourth-moment charge.
2. `MaynardPrattTypeIIPacking.lean`
   - finite greedy separation and coverage;
   - analytic-multiplicity-preserving count reduction.
3. `MaynardPrattTypeIILocalZeroCount.lean`
   - an injection into the xi divisor;
   - a positive reciprocal-mass charge at `2+i*t`;
   - the source local occupancy bound `ceil(30*(log T)^7)`.
4. `MaynardPrattTypeIIGlobalCharge.lean`
   - centered-to-absolute window translation;
   - pairwise-disjoint source windows;
   - charging to the global interval `[T/2,3T]`;
   - a uniform `Y^(1/2-sigma)` local coefficient;
   - the conditional full-count composition.

The exact open predicate is:

```text
MaynardPrattTypeIISourceTwistedFourthMomentEstimate A
```

which states eventually

```text
integral_[T/2,3T] |M(1/2+it) * zeta(1/2+it)|^4 dt
  <= T * (log T)^A
```

for `M=floor(2*T^(1/100))`.

## Source-display falsification and repair

The arXiv v2 proof states the contour `Re(s)=1/2-beta` but then displays
`Gamma(beta-1/2+i*u)`. Direct substitution gives `Gamma(1/2-beta+i*u)`.

Lean proves that the two arguments are unequal when `beta>1/2`. It also proves the recurrence
repair

```text
(beta-1/2) * |Gamma(1/2-beta+i*u)| <= 2,
```

and therefore the source range
`beta>=sigma>=1/2+1/log T` recovers the required bound

```text
|Gamma(1/2-beta+i*u)| <= 2*log T.
```

The displayed source formula is falsified; the logarithmic consequence used by the consumer is
repaired.

## Historical omission result

The local zero-count consumer does not require a full Riemann--von Mangoldt reconstruction.
Positivity of the xi divisor reciprocal terms at `2+i*t`, together with the right-half-plane
Euler-product logarithmic derivative, supplies a sufficient multiplicity-bearing
polylogarithmic occupancy bound.

This is a premise reduction inside the historical argument. It is not a new zero-density
estimate and does not change the unconditional RH frontier.

## Short-moment omission probes

The preregistered weaker routes were tested in order.

### Direct finite mean square

Squaring the source mollifier gives length about `T^(1/50)`. A critical-line approximate
functional equation for `zeta^2` has natural length about `T`. Their product therefore has
generic length about `T^(1+1/50)`. An `O(interval length + polynomial length)` mean square
retains a positive power loss and does not prove `T*(log T)^A`.

### Upper-bound-only approximate functional equation

Splitting `zeta` at square-root length makes `M*zeta` a polynomial of length about
`T^(1/2+1/100)`. Its fourth moment is again a mean square at squared length
`T^(1+1/50)`. The same power overshoot remains.

### Watt shortcut

Writing `|M|^4=|M^2|^2` puts the integral into the shape of Watt's twisted fourth-moment
upper bound. In Watt's `sum a_m*m^(-it)` normalization, the coefficients of `M^2` are the
truncated Mobius-convolution coefficients divided by `sqrt(m)`, so their maximum admits a
coarse absolute bound. But the theorem still multiplies that maximum by the polynomial
length `T^(1/50)` and by `T^(1+epsilon)`. It therefore gives a positive power loss rather
than the fixed polylogarithmic estimate required here.

An operator estimate using the coefficient square-sum in place of length times maximum
squared coefficient would fit the Mobius convolution much better, but no such compiled or
source-independent Watt theorem was found. Formalizing that stronger operator estimate would
re-enter the deep spectral/Kloosterman machinery.

### Cited fallback

Hughes--Young and Bettin--Bui--Li--Radziwill prove arbitrary-polynomial twisted fourth-moment
asymptotics strong enough for the source. Heap--Radziwill--Soundararajan Proposition 5.1 is not
an independent weaker proof; its proof invokes the Bettin--Bui--Li--Radziwill asymptotic.

No smaller source-backed proof of the fixed polylogarithmic moment was found in this campaign.

## Exact surviving gap

`OBS-H2-SOURCE-MOBIUS-TWISTED-FOURTH-MOMENT-01` remains open. It can be attacked later by:

- a genuinely coefficient-`L2` twisted fourth-moment upper bound at length `T^(1/50)`;
- a source-specific shifted-convolution estimate for the truncated Mobius square;
- or formal reconstruction of the cited Hughes--Young/BBLR asymptotic at the required
  specialization.

The final normalization of the already compiled exact charge factors to
`T^(2*(1-sigma))*(log T)^B` is elementary postprocessing after an exponent `A` is fixed.

## Audit and public evidence

- Standalone production module: pass without warnings.
- Target build: `8724/8724`.
- Full project build: `8810/8810`, with only inherited warnings.
- Exact `TargetChecks`: five.
- Registered selected axiom prints: seven, all using only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: empty.
- Implementation commit:
  `b44255fdeb49f12a55214888d26c40d761dfe8e5`.
- Implementation CI:
  run `30505660293`, job `90754736822`, `2m49s`, pass.
- Receipt commit:
  `053314b50bc1fe010c87f313db04bc6e7bb0eae1`.
- Receipt CI:
  run `30505893693`, job `90755448680`, `1m36s`, pass.

## Claim boundary

This result proves no Type-II rarity estimate, no full zero-density theorem, no Type-I rarity,
no bow exclusion, no H2, no zero-free region, and no RH. It freezes an audited source repair,
a smaller local-zero-count producer, and the exact remaining analytic theorem before
cross-family reranking.
