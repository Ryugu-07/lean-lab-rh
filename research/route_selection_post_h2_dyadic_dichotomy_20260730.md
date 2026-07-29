# Route Selection after the H2 Classical Detector Dyadic Dichotomy

Date: 2026-07-30

Status: `H1_HARDY_LITTLEWOOD_ETA_REMAINDER_SELECTED / PREREGISTRATION_LOCAL`

## Closed parent

Campaign `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01` is publicly
closed at receipt commit `d85a370e4adaffdcf51e86fa8b38ff459518d491`, Lean Action run
`30492021514`, build job `90711944691`, passed in `1m38s`.

The closed H2 node proves the actual source-scale Type-I/Type-II detector dichotomy. Its next
edges are the global rarity estimates for the two alternatives, not a further finite
decomposition.

## Selection rule

Historical-route work is an omission search. A route is not counted as explored merely because
its name, equivalence, or finite consumer has been formalized. We follow the route to its first
real unavailable inference and ask whether a human premise was stronger than necessary, two
arguments can be combined, or a small finite mechanism was hidden inside a global proof.

Original conjectures, falsification, and direct RH proof attempts remain open at every stage.
Numerical optimization is not selected unless a number controls a genuine logical threshold.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1 Hardy--Littlewood 1921 | Prove Lemma 3's uniform eta remainder for `abs(t)<A*N` without an `abs(s)` loss, then identify the ordered limit with `(1-2^(1-s))*zeta(s)`. | The exact downstream Abel transfer and finite mean square already compile. The source proof hides a two-scale main-term cancellation, while a direct moving-ratio summation may isolate an even smaller finite mechanism. | **Select.** |
| H1 Selberg / Levinson--Conrey | Produce the global mollified moments and actual auxiliary-function zero counts. | The local sign detector compiles, but the next source estimates remain broad global mean-value theorems. | Retain open. |
| H2 Ingham--Huxley / Maynard--Pratt | Prove Type-I block rarity and Type-II shifted-integral rarity uniformly over actual zeros. | The actual detector dichotomy now compiles. The next step is a full density argument rather than a bounded omitted inference. | Retain open. |
| H10 Bombieri--Stepanov | Instantiate curve divisors, Riemann--Roch dimensions, and the zero-versus-pole multiplicity budget. | The finite auxiliary-polynomial consumers compile, but Mathlib does not yet expose the required complete-curve divisor stack as a source-ready theorem. | Retain as a high-value geometry campaign. |
| H12 Levinson--Montgomery | Assemble the multiplicity-aware indented argument principle, top Jensen variation, and signed bottom orientation. | The boundary and dense-branch modules compile. The remaining source inference is decisive but global and has three coupled analytic inputs. | Retain as a high-value global campaign. |
| H7/H8 spectral | Construct the actual arithmetic operator or xi-bearing Hilbert space with convergence and positivity. | Abstract and finite consumers compile; the missing source object remains global. | Retain open. |
| H11 zero statistics | Amplify a statistic so that a sparse persistent off-line orbit cannot escape. | Existing normalized statistics formally tolerate finite or density-zero exceptions. | Retain open. |

H1 is selected because it has a fixed source statement, an existing compiled consumer, and a
new finite proof candidate. This is not a return to constant optimization.

## Primary-source reconstruction

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), pages 284--286:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.
- Audited PDF SHA-256:
  `050b62cc3ed048e335d27bb93804340c03f70f94d2f5a1f7f6e95873647312ec`.

Lemma 2 proves, for `sigma>=sigma0>0`, away from the zeta pole and under
`abs(t)<2*pi*x/C`,

```text
zeta(s) = sum_(n<=x) n^(-s) - x^(1-s)/(1-s) + O(x^(-sigma)).
```

Lemma 3 subtracts `2^(1-s)` times the same formula at `x/2`. The two principal terms cancel
exactly, giving

```text
eta(s) = (1-2^(1-s))*zeta(s)
       = sum_(n<=x) (-1)^(n-1)*n^(-s) + O(x^(-sigma)).
```

Thus the source contains no separate `abs(s)`-sized eta error. The apparent loss from pairing
adjacent terms is an artifact of taking absolute values too early.

## Omission candidate

Write the unit-modulus part of the alternating term as `u_n`. Consecutive terms satisfy

```text
u_(n+1) = q_n*u_n,
q_n = -exp(-i*delta_n),
delta_n = t*log(1+1/n).
```

When `abs(t)<=N` and `n>=N`, `q_n` stays uniformly near `-1`. Set
`c_n=(1-q_n)^(-1)`. Then

```text
u_n = c_n*(u_n-u_(n+1)).
```

Summing telescopes. The chord estimate
`norm(exp(i*x)-1)<=abs(x)`, monotonicity of `log(1+1/n)`, and the variation of `c_n` should give
a uniform finite bound for every phase block. A second finite Abel transform against
`n^(-sigma)` would then give the actual `O(N^(-sigma))` eta tail without first formalizing the
full Fourier-integral proof of Lemma 2.

This is a proof candidate, not a claimed theorem. Lean must check the ratio identity,
denominator separation, total variation, weighted tail, convergence, and analytic
identification.

## Fixed next campaign

- `campaign`: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`.
- `node`: `H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `fixed_endpoint`: prove a uniform finite phase-block bound from the actual logarithmic
  ratios; derive ordered eta convergence and an explicit `C*N^(-sigma)` remainder for
  `sigma>0` and `abs(t)<=N`; identify the limit with the project's
  `hardyLittlewoodEta s=(1-2^(1-s))*riemannZeta s` away from `s=1`; and compose the result with
  the compiled eta-to-Theta transfer.
- `negative_control`: existence of an unnamed ordered limit, a bound with an `abs(s)` factor,
  or a theorem assuming Hardy--Littlewood Lemma 2 does not count as full success.
- `strict_boundary`: no eta-error second moment, source-X moving-window moment, parameter
  budget, unconditional linear count, H1, or RH.
- `production_gate`: no `LeanLab/` proof or registration edit before docs-only
  preregistration passes public CI.

The persistent RH Goal remains active.
