# H1 Hardy--Littlewood Linear Count Closure Receipt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01`

Node: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`

Classification: `FULL_SUCCESS / FINITE_EXCEPTIONAL_SET_COUNT_BRIDGE_FORMALIZED`

## Verified public chain

| gate | commit | run | job | result |
| --- | --- | --- | --- | --- |
| docs-only preregistration | `d36f9d0c8005691e9043165c062bf60a9e311722` | `30438867401` | `90533061533` | success in `1m57s` |
| frozen implementation | `8f3742c62a381293fa201358cf58130d2c333c48` | `30464674314` | `90619318156` | success in `2m52s` |
| immutable evidence | `9f161104ed086a137e221b6c8ffe3d3bdda65005` | `30465073931` | `90620648692` | success in `2m14s` |
| final ledger | `25316ea1b408731da6581a371afcaccd2bf169f7` | `30465345680` | `90621575136` | success in `1m41s` |

The five proof and registration files have an empty diff from the frozen implementation through
the final ledger.

## Closure

Close only:

```text
H1.hardy-littlewood.exceptional-set-linear-count
```

Lean proves the finite Hardy--Littlewood chain:

```text
two square-moment estimates
-> a small bad-start set
-> strict integral gaps at good starts
-> a whole length-H charge for every failed adjacent pair
-> a natural lower bound for good pairs
-> injective actual critical-line zeta-zero ordinates.
```

The exact aggregate theorem is `hardyLittlewood_source_finite_count`. The lower estimate is
required only on `[T,2T]`, and endpoint-only sampling is rejected by a compiled null-set
countermodel.

Keep open:

- the actual source Hardy `X/Z` normalization and exact zero adapter;
- Hardy--Littlewood's eta lower estimate and its error second moment;
- the source-coordinate moving-integral second moment;
- the asymptotic parameter budget producing unconditional `N_0(T) >> T`;
- Selberg's global moment producer and positive-proportion theorem;
- the Levinson--Conrey auxiliary count;
- sparse-exception elimination, H1, and RH.

The persistent RH Goal remains active. After this receipt is public green, stop only this local
campaign and rerank the historical families by omission value. Original conjectures,
falsification, and direct RH attacks remain open at every selection.
