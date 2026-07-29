# H1 Hardy--Littlewood Source Normalization Closure Receipt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-01`

Node: `H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-ETA-LOWER-01`

Classification: `FULL_SUCCESS / SOURCE_NORMALIZATION_ETA_LOWER_FORMALIZED`

## Verified public chain

| gate | commit | run | job | result |
| --- | --- | --- | --- | --- |
| docs-only preregistration | `65dc6f89905e52deaac1c22a65a2f7ea745a124e` | `30468092999` | `90631003060` | success in `1m37s` |
| frozen implementation | `728acf822fad197fa4f60bd3f89fe502863b830a` | `30468913754` | `90633769051` | success in `2m43s` |
| immutable evidence | `d3af00a675bf4e99f422a230630e2877a9d266f9` | `30469279435` | `90634996505` | success in `2m0s` |
| final ledger | `0bb0b20f07717a72fbefb397d5f70e4876f03e57` | `30469539221` | `90635882124` | success in `2m16s` |

The five proof and registration files have an empty diff from the frozen implementation through
the final ledger.

## Closure

Close only:

```text
H1.hardy-littlewood.source-normalization-eta-lower
```

Lean proves the source-faithful chain:

```text
positive global extension of the 1921 source coordinate
-> exact actual critical-line zero adapter
-> exact project xi/Gamma/zeta norm identity
-> explicit H6-remainder Gamma lower estimate
-> zeta and eta pointwise lower estimates
-> exact eta primitive identity
-> absolute-window lower premise on [T,2T].
```

The exact aggregate theorem is `hardyLittlewoodSourceNormalization_endpoint`. The literal
positive-height source weight is preserved for `t>=1`; the low-height extension repairs global
positivity. The naive symmetric raw weight is formally zero at `t=0`.

Keep open:

- identification of the eta integral primitive with the relevant component of the Lemma 7
  Dirichlet series;
- the eta-window error square-mean estimate;
- the actual source-coordinate moving-integral square-mean estimate of Lemma 11;
- the asymptotic parameter budget needed by `hardyLittlewood_source_finite_count`;
- the unconditional Hardy--Littlewood linear count;
- Selberg's global moment producer and positive-proportion theorem;
- the Levinson--Conrey auxiliary count;
- sparse-exception elimination, H1, and RH.

The persistent RH Goal remains active. After this receipt is public green, stop only this local
campaign and rerank the historical families by omission value. Original conjectures,
falsification, and direct RH attacks remain open at every selection.
