# Route Selection after H7 Rayleigh-Gap

Date: 2026-07-23

Status: `H1_THETA_INFINITY_CONSUMER_SELECTED / PREREGISTRATION_CI_REQUIRED`

## Closed parent campaign

Campaign `DISCOVERY-20260723-H7-PROLATE-RAYLEIGH-GAP-01` is publicly closed at final-ledger
commit `5e36c53da657b4018f23339d4744562da07002ba`, public Lean Action run `29965855724`, build job
`89077075898`, in `1m51s`. Its generic Rayleigh-gap consumer and collapsing-gap obstruction are
proved. The concrete arithmetic/prolate ratio, H7, and RH remain open.

## Governing interpretation

The historical atlas is a mechanism inventory, not a one-campaign-per-family completion list.
Historical work must reconstruct the strongest actual implication of a route and look for omitted
edges. Original conjectures and direct RH attacks remain open at every selection, but no open
candidate may be used as a premise.

## Route-map correction

The current D3 card says that long mollification aims at critical-line proportion one and then
faces a sparse-exception barrier. That is correct for a bare density-one conclusion but incomplete
for Farmer's full `theta=infinity` conjecture.

Bettin--Gonek, arXiv:1604.02740, prove a pointwise zero-exclusion theorem. For fixed `theta > 0`,
the source hypothesis

```text
I_N(0,T) <<_epsilon T^(1+epsilon), uniformly for 2 <= N <= T^theta,
```

forces zeta to have no zero in

```text
Re(s) > 1/2 + 1/(2*theta).
```

Allowing arbitrarily large `theta` therefore implies RH directly, rather than passing only through
an asymptotic proportion-one statement. The proof attaches a power-growth obstruction to each
individual off-line zero. This is exactly the kind of historical mechanism the survey is intended
to recover.

## Cross-route comparison

| candidate | new information | discriminating next probe | verdict |
| --- | --- | --- | --- |
| H1 Farmer--Bettin--Gonek | A published arbitrary-length mollifier hypothesis excludes every individual zero to the right of a moving boundary and implies RH as `theta -> infinity`. This direct edge was absent from the current route card. | Align the real-cutoff mollifier, close the integer-to-real cutoff step used under the source integral, and compile the final exponent squeeze. | `SELECTED` |
| H7 source Rayleigh ratio | The generic consumer is proved, but actual arithmetic entries, prolate coefficients, and the ratio limit are not yet available. | Instantiate and numerically falsify the source ratio before another proof attempt. | `OPEN`; no immediate source data layer. |
| H2 bow exclusion | The symmetry-only shortcut is falsified; actual arithmetic amplification remains unnamed. | Find a source localizer that detects one bow. | `OPEN`; lower current leverage. |
| H10 function-field transfer | Finite spectral rigidity is compiled, while the number-field trace/cohomology object is missing. | Identify an actual transfer theorem, not an analogy. | `MONITOR`. |
| Direct Weil/Li/closure | Exact consumers exist, but the unconditional positivity/closure input is RH-strength. | Enter whenever a new arithmetic sign mechanism is named. | Always eligible. |

## Locked primary sources

1. Bettin--Gonek, *The theta=infinity conjecture implies the Riemann hypothesis*,
   arXiv:1604.02740, Theorems 1 and 2 and equations `(2.1)`--`(2.5)`.
   <https://arxiv.org/abs/1604.02740>
2. Farmer, *Long mollifiers of the Riemann zeta-function*, Mathematika 40 (1993), 71--87.
   <https://doi.org/10.1112/S0025579300013723>
3. Radziwill, *Limitations to mollifying zeta(s)*, arXiv:1207.6583.
   <https://arxiv.org/abs/1207.6583>
4. Conrey--Farmer--Kwan--Lin--Turnage-Butterbaugh, *Short mollifiers of the Riemann zeta-function*,
   arXiv:2508.11108, for the modern route placement and its explicit citation of the
   Bettin--Gonek implication.
   <https://arxiv.org/abs/2508.11108>

## Source proof spine and exact gap

The source defines

```text
M_x(s) log x = sum_(n <= x) mu(n) n^(-s) log(x/n)
I_x(T1,T2) = integral_[T1,T2] |M_x(1/2+it) zeta(1/2+it)|^2 dt.
```

For an assumed zero `rho0 = beta0 + i*gamma0`, Mellin inversion and contour shifting produce a
residue term of order `x^(beta0+1/2)`. Cauchy--Schwarz and the critical-line zeta second moment
then give, after `x = T^theta`,

```text
T^(2*beta0*theta) <<_epsilon T^(1+epsilon+theta).
```

The final exponent comparison yields `beta0 <= 1/2 + 1/(2*theta)`. The hard formalization gap is
the analytic passage from the exact moment hypothesis to this power obstruction: Mellin inversion,
holomorphy and decay of the auxiliary transform, contour movement across the selected zero,
uniform constants, and the zeta second-moment lower bound.

One smaller quantifier edge deserves explicit checking. The theorem states a uniform hypothesis in
integer `N`, while the proof extends `M_x` to real `x` and integrates `I_y` over real `y`. Between
successive integers, the normalized mollifier is affine in `1/log y`; a convex interpolation bound
should close this passage. The identity must be compiled rather than silently assumed.

## Decision

Preregister campaign `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01`. It will formalize the
exact source objects, integer-to-real interpolation, and exponent/zero-free consumers. It will not
claim the moment-to-power analytic bridge, Farmer's conjecture, or RH. A successful endpoint opens
a separate mechanism-level campaign on equations `(2.2)`--`(2.5)` rather than another numerical
proportion optimization.
