# Route Selection after the H1 Eta-Primitive Mean Square

Date: 2026-07-30

Status: `H2_MAYNARD_PRATT_TYPE_II_RARITY_SELECTED / PREREGISTRATION_LOCAL`

## Closed parent

Campaign `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`
is publicly closed at receipt commit `dd593af9c0a838016f4ca954221dc7408a9d662a`,
Lean Action run `30500121527`, build job `90737729961`, passed in `1m56s`.

The closed node reconstructs the consumer-strength form of Hardy--Littlewood Lemma 7. It shows
that the public eta remainder and a finite `O(L+N)` mean square suffice; the stronger Lemma 8
asymptotic is not needed for that edge.

## Selection rule

Historical-route work is an omission search. The next route should expose a first real
human-source inference, test whether its published premises are stronger than its consumer
requires, and retain failed attempts as obstacle evidence. Family adjacency and numerical
constant optimization are not selection reasons.

Original conjectures, falsification, and direct RH proof attempts remain open at every stage.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H2 Maynard--Pratt Type II | Prove rarity of actual Type-II shifted integrals. | The actual source-scale Type-I/II dichotomy compiles. The source's next Lemma 24 is a complete branch whose only deep input is a twisted fourth-moment upper bound for one Mobius polynomial of length `2*T^(1/100)`, much weaker than the cited general asymptotics. | **Select.** |
| H1 Hardy--Littlewood 1921 | Prove the source-X moving-window moment and close the parameter budget. | This remains important, but the last two H1 campaigns already tested the newly opened eta interface. Cross-family omission coverage now has higher value. | Retain open. |
| H1 Selberg / Levinson--Conrey | Prove long mollified moments and the multiplicity-aware auxiliary count. | The next producer is a broad off-diagonal mean-value theorem; no new bounded interface appeared in this rerank. | Retain open. |
| H10 function field | Build actual curve-divisor, Riemann--Roch, and Frobenius point-count inputs. | The finite spectral and Hodge consumers compile, but the source-ready algebraic-geometry stack is still absent. | Retain as required historical work. |
| H11 zero statistics | Amplify one sparse off-line orbit to absolute statistical mass. | Existing pair and moving-window consumers still permit finite or density-zero exceptions. | Retain open. |
| H12 Speiser / counts | Assemble the global indented argument principle, Jensen top bound, and signed boundary orientation. | The decisive edge remains a three-input global contour theorem rather than a newly exposed omission. | Retain open. |
| H7/H8 spectral / entire geometry | Construct the actual arithmetic operator or xi-bearing Hardy space and prove convergence. | Abstract consumers are deep, but the missing concrete source objects remain global. | Retain open. |

H2 is selected because the previous H2 campaign reached the exact input of a named source
lemma. This is an attack on a global rarity estimate, not another finite detector wrapper.

## Primary-source reconstruction

Primary source:

- James Maynard and Kyle Pratt, *Half-isolated zeros and zero-density estimates*,
  Section 5 and Appendix C, Lemma 24:
  <https://arxiv.org/abs/2206.11729>.

For a Type-II zero `rho=beta+i*gamma`, the source changes variables in the shifted Mellin
integral and obtains a lower bound for

```text
integral |Gamma(-1/2+beta+i*u)|
  * |M(1/2+i*gamma+i*u) * zeta(1/2+i*gamma+i*u)| du.
```

Gamma decay truncates to `|u| <= (log T)^2`. Holder then charges every Type-II zero by local
fourth-moment mass. A `(log T)^3`-separated subfamily turns the local sum into one global
integral, and the source invokes

```text
integral_(T/2)^(3T) |M(1/2+i*t) * zeta(1/2+i*t)|^4 dt
  <= T * (log T)^O(1).
```

The cited general inputs include Hughes--Young,
<https://arxiv.org/abs/0709.2345>, and Bettin--Bui--Li--Radziwill,
<https://arxiv.org/abs/1609.02539>. Their arbitrary-polynomial asymptotics permit lengths
`T^(1/11-epsilon)` and `T^(1/4-epsilon)`, respectively. The Maynard--Pratt consumer uses only
the fixed truncated-Mobius polynomial of length `2*T^(1/100)` and only an upper bound.

## Omission candidate

Test whether the specific short-mollifier upper bound can be proved through a smaller theorem
than the full twisted fourth-moment asymptotic. The exact source chain should be formalized
before attempting that producer, so Lean distinguishes:

1. Type-II shifted-integral largeness;
2. local fourth-moment charging;
3. multiplicity-aware separated packing;
4. the one specific global twisted fourth moment;
5. the final exponent `T^(2*(1-sigma))`.

If the global moment cannot be produced, the campaign must name it as an open analytic input.
Packaging it as a hypothesis is not a Type-II rarity theorem.

## Fixed next campaign

- `campaign`: `LITERATURE-20260730-H2-MAYNARD-PRATT-TYPE-II-RARITY-01`.
- `node`: `H2-MAYNARD-PRATT-TYPE-II-RARITY-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `full_endpoint`: prove an explicit eventual multiplicity-bearing version of Maynard--Pratt
  Lemma 24 for the actual source Type-II predicate and literal source mollifier.
- `omission_probe`: attempt the required fixed-mollifier fourth-moment upper bound without
  formalizing the cited arbitrary-polynomial asymptotic.
- `meaningful_partial`: the exact local charge, separated packing, and conditional exponent
  theorem may compile only if every unproved producer remains an explicit named premise.
- `negative_control`: a generic Markov inequality, an unweighted zero count, or an assumed
  twisted fourth moment is not full success.
- `strict_boundary`: no Type-I rarity, bow exclusion, density theorem for all zeros, H2,
  zero-free statement, or RH.
- `production_gate`: no `LeanLab/` proof or registration edit before docs-only
  preregistration passes public CI.

The persistent RH Goal remains active.
