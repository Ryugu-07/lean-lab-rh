# Route Selection after the H1 Hardy--Littlewood Eta Remainder

Date: 2026-07-30

Status: `H1_HARDY_LITTLEWOOD_ETA_PRIMITIVE_MEAN_SQUARE_SELECTED / PREREGISTRATION_LOCAL`

## Closed parent

Campaign `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01` is publicly closed at
receipt commit `5bce854bcfbcb30b8f27c1ff629d6311792c5614`, Lean Action run
`30496464584`, build job `90726356672`, passed in `1m45s`.

The closed node proves Hardy--Littlewood Lemma 3's actual eta remainder
`4*N^(-sigma)`, identifies the ordered series with
`(1-2^(1-s))*riemannZeta(s)`, specializes to the critical line, and supplies the existing
eta-to-Theta consumer.

## Selection rule

Historical-route work remains an omission search. A route earns priority when a source-exact
inference has newly compiled predecessors and consumers, when a stronger human premise may be
weakened, or when two previously separate routes now meet. Family adjacency and numerical
constant improvement are not selection reasons.

Original conjectures, falsification, and direct RH proof attempts remain open at every stage.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1 Hardy--Littlewood 1921 | Identify the eta integral primitive with the logarithmically weighted series and prove Lemma 7's shifted `L2=O(T)` estimate. | Lemma 3, the eta-to-Theta transfer, and a weaker finite `O(L+N)` mean square now compile independently. They may suffice for the exact source moment without the stronger Lemma 6 saving or Lemma 8 asymptotic. | **Select.** |
| H1 Selberg / Levinson--Conrey | Prove the actual mollified global moments and multiplicity-aware auxiliary zero count. | The local sign and step geometry compile, but the next source estimates remain broad long-polynomial mean values. | Retain open. |
| H2 density | Prove rarity of the actual Type-I and Type-II alternatives. | The detector and dyadic disjunction compile; the next inputs are global large-value estimates, not a bounded missing inference. | Retain open. |
| H7/H8 spectral and de Branges | Prove the actual exponentially weighted ground-state comparison or construct the concrete xi Hardy RKHS. | The required source objects and global convergence remain absent. | Retain open. |
| H10 function field | Instantiate actual curve valuations, Riemann--Roch dimensions, and the pole divisor, or produce a number-field consumer. | The finite Frobenius and noncancellation mechanisms compile, but further known geometry currently has no number-field transfer consumer. | Retain as a required historical branch. |
| H11 zero statistics | Upgrade normalized pair statistics to absolute strength or amplify one sparse off-line orbit. | The exact horizontal-multiplicity and moving-window consumers compile; current source errors still permit finite or density-zero exceptions. | Retain open. |
| H12 Speiser / counts | Assemble the global indented argument principle, Jensen top variation, and signed boundary orientation. | The remaining source inference is decisive but couples several global analytic inputs. | Retain open. |

H1 is reselected for a materially new reason: the newly public Lemma 3 theorem closes the
infinite-series truncation gap that previously prevented the finite mean-square theorem from
reaching Hardy--Littlewood Lemma 7. This is not optimization of the phase constant `4`.

## Primary-source reconstruction

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), pages 287--288:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.
- Audited PDF SHA-256:
  `050b62cc3ed048e335d27bb93804340c03f70f94d2f5a1f7f6e95873647312ec`.

Lemma 7 defines

```text
psi(t) = sum_(n>=2) (-1)^(n-1) * n^(-1/2-i*t) / log(n)
```

and proves

```text
integral_(T to 2T) |psi(t+u)|^2 dt = O(T)
```

uniformly for `0<=u<=T`. Lemma 8 records a stronger mean-square asymptotic for the same
Dirichlet series. The later sign-count argument needs an upper moment bound for the eta
primitive error, not that full asymptotic.

## Omission candidate

Define the canonical ordered value of the already compiled
`hardyLittlewoodThetaPartialSum`. On the critical line it is the source `psi`. The finite
partial sums satisfy the exact differential identity

```text
d/dt psi_N(t) = -i * (eta_N(1/2+i*t) - 1),
```

so the project primitive should be

```text
hardyLittlewoodEtaPrimitive(t) = -Im(psi(t)-psi(0)).
```

For `t in [T,2T]` and `0<=u<=T`, choose a truncation `N>=3T`. The compiled eta-to-Theta
remainder is then uniform in `t+u`, while the finite theorem bounds the polynomial mean square
by `O(T+N)=O(T)`. A square-triangle bound should pass this to the infinite series. Applying the
same estimate at shifts `0` and `H` should give the exact eta-window-error moment needed by
`hardyLittlewood_source_finite_count`.

Lean must check the series normalization, derivative sign, primitive limit passage, cutoff
rounding, uniform shifted tail, interval integral, and restricted `lintegral` consumer.

## Fixed next campaign

- `campaign`:
  `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`.
- `node`: `H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `fixed_endpoint`: construct the canonical source `psi`; identify
  `hardyLittlewoodEtaPrimitive` with `-Im(psi(t)-psi(0))`; prove an explicit
  `Cpsi*T` shifted mean-square bound for `T>=1`, `0<=u<=T`; derive an explicit
  `Beta*T` restricted-measure square moment for
  `hardyLittlewoodEtaWindowError H` when `0<=H<=T`; and expose the exact existing finite-count
  premise.
- `negative_control`: pointwise convergence, an unshifted-only estimate, a bound whose constant
  depends on `T` or `u`, or an assumed primitive identity is not full success.
- `strict_boundary`: no source-X moving-window moment, parameter budget, unconditional linear
  count, H1, or RH.
- `production_gate`: no `LeanLab/` proof or registration edit before docs-only
  preregistration passes public CI.

The persistent RH Goal remains active.
