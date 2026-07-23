# H7 Weil Pole Block Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H7-WEIL-POLE-BLOCK-01`

Status: `LOCAL_MECHANICAL_CLOSURE / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Source coordinates

Primary source: Groskin, arXiv:2607.02828, Section 2, the source pole function and the proof of
the entry identification lemma. The closed matrix agrees there with Connes--Consani--Moscovici,
arXiv:2511.22755, Lemma 4.1.

For `c>1`, the source parameters are

```text
L = log c,
beta = L/(4*pi),
C_c = L*(sqrt c + 1/sqrt c - 2)/(2*pi^2).
```

## Object map

| source object | Lean object | alignment |
| --- | --- | --- |
| `beta` | `weilPoleBeta c` | Literal source formula. |
| `C_c` | `weilPoleCoefficient c` | Literal source formula; Lean proves strict positivity for `c>1`. |
| centered integer frequency `k` | `weilPoleFrequency N i` | Real cast of the already audited centered `Fin (2*N+1)` coordinate. |
| `psi_0(k)` | `weilPoleSourceValue c N i` | Literal rational source value sample. |
| `psi_0'(k)` | `weilPoleSourceDerivative c N i` | Literal derivative/diagonal sample. |
| source pole divided difference | `weilFinitePoleSourceMatrix c N` | Constructed through the existing generic divided-difference matrix, not by assuming the closed answer. |
| closed pole entry | `weilFinitePoleClosedEntry c N i j` | Exact source formula for diagonal and off-diagonal entries. |
| even pole vector | `weilFinitePoleEvenVector c N` | `beta/(k^2+beta^2)`, proved reflection-even. |
| odd pole vector | `weilFinitePoleOddVector c N` | `k/(k^2+beta^2)`, proved reflection-odd. |

## Compiled result

Lean proves the all-entry identity

```text
Q_pole(i,j) =
  C_c*(beta^2-k_i*k_j)
  / ((k_i^2+beta^2)*(k_j^2+beta^2)),
```

including the source derivative on the diagonal. It then proves

```text
Q_pole = C_c*(|e><e| - |o><o|)
```

and, for every finite real vector `x`,

```text
x dot (Q_pole*x) = C_c*((e dot x)^2-(o dot x)^2).
```

Since `C_c>0`, this quadratic form is nonnegative on reflection-even vectors and nonpositive on
reflection-odd vectors. Thus the source pole block has the exact opposite parity signs required
by the Herglotz rank-one presentation. No factor, centered-frequency sign, or diagonal-limit
mismatch was found.

## Claim boundary

The pole sign law is not positivity of the total Weil matrix. In fact, the odd pole term is
nonpositive. Any total parity ordering must use the prime and archimedean blocks together with
this rank-two term. The module proves no arithmetic Herglotz scalar bound, simple-even theorem,
uniform cutoff theorem, ground-state/prolate comparison, transform convergence, H7, or RH.

## Mechanical status

- Production module: 250 lines, standalone diagnostic-free compile.
- Module build: 8,650 jobs passed.
- Targets: one new proven actual-source-block Target; the source ratio Target remains open.
- Exact TargetChecks: 9 new witnesses compile.
- Axiom audit: 7 selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Production forbidden scan: empty.
- Direct compiles: production module, Targets, TargetChecks, and AxiomsAudit pass.
- Full build: 8,753 jobs passed.
- `rh_frontier_delta=0`; `hard_gap_delta=0`; `actual_source_block_delta=1`.
