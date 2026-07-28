# Route Selection after H1 Hardy Theta Inversion

Date: 2026-07-28

Status: `RERANK_COMPLETE / H12_SPEISER_ADMISSIBLE_CONTOUR_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H1-HARDY-THETA-INVERSION-01` is publicly closed at
final-ledger commit `183ace2f83deb2a5c5654761b74e2ca7a2d50202`, Lean Action run
`30379640249`, build job `90344021329`, in `2m36s`.

The frozen implementation proves Hardy's exact 1914 Cahen--Mellin equation (1) for every
positive real input. The first unproved continuation edge is compact-substrip
exponential-weight integrability of the actual `Xi(2t)` kernel. That H1 node remains open, but
fresh selection is required instead of continuing the same analytic estimate by inertia.

## Historical-family reconciliation

The five-family summary supplied by the user is directionally useful but no longer describes
the repository's actual coverage:

- H1 now contains the complete conditional Farmer--Bettin--Gonek individual-zero bridge and the
  exact Hardy positive-real inversion, while Farmer's arbitrary-length moment and Hardy's strip
  continuation remain open.
- H7 has finite-prime Weil dictionaries, finite operators, admissibility audits, and explicit
  spectral obstructions; the infinite arithmetic operator and convergence remain open.
- H10 has finite spectral rigidity and Bombieri--Stepanov Frobenius/polar mechanisms, while the
  actual curve Riemann--Roch construction and number-field transfer remain open.
- H11 has horizontal-multiplicity, triangular pair mass, and exact moving-window boundary
  bookkeeping; absolute-error control of one sparse exception remains open.
- H12 Speiser/Levinson--Montgomery is a distinct historical family omitted by the five-family
  summary. Its local zero-mass, boundary-sign, and critical-line indentation mechanisms compile,
  but the global count theorem does not.

The survey therefore continues by exact surviving edges, not by the older coarse coverage
labels.

## Fresh cross-family comparison

| family | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H12 Speiser | Complete Levinson--Montgomery Theorem 1 for actual multiplicity-bearing zeta and zeta-derivative counts. | The 1974 proof fixes its bottom at `t=10` using a low-zero verification. The asymptotic count comparison should only need one fixed common zero-free bottom; its contribution is a `T`-independent constant. This weakening has not been tested in Lean. | **Select.** |
| H10 function field | Build the actual curve zero--pole budget and Riemann--Roch/Frobenius dimension selection. | Historically central and underformalized, but current Mathlib has no source-ready curve divisor degree or Riemann--Roch theorem. Retain as a high-value geometry campaign rather than replace it with an abstract budget axiom. | Runner-up. |
| H1 Levinson--Conrey | Reconstruct the proportion count and actual mollified mean value. | The structural route remains underformalized, but the decisive long/off-diagonal estimate has no new unconditional input. Another variational optimum would be numerical proportion optimization. | Retain open. |
| H2 density | Exclude an actual slowly bending bow of zeta zeros. | The finite obstruction is compiled; no source theorem supplies the missing arithmetic rigidity. | Retain open. |
| H7 spectral/Weil | Construct the infinite arithmetic operator and preserve ground-state orientation. | High direct value, but the missing object and tail theorem remain broad after multiple finite campaigns. | Retain open. |
| H11 statistics | Upgrade density-scale pair correlation to exclude one sparse orbit. | The exact boundary is compiled; current analytic errors still absorb a fixed exception. | Retain open. |
| H13 generalized L-functions | Transfer a proved family or nonarchimedean mechanism to the individual zeta zero set. | Existing family and extra-factor audits show no direct transfer theorem. | Monitor. |

## The omission probe

Levinson and Montgomery, *Zeros of the derivatives of the Riemann zeta-function*, Acta
Mathematica 133 (1974), Theorem 1, prove

```text
N_zeta'(T) = N_zeta(T) + O(log T)
```

in the upper-left half of the critical strip, followed by the exact-count/dense-count
dichotomy that yields Speiser's criterion. In their proof of Theorem 1 they establish
`Re(zeta'/zeta)<0` on the fixed lower boundary `t=10`, using the then-known verification that
the low nontrivial zeros lie on the critical line.

For the count asymptotic, a fixed lower boundary need not carry a uniform sign if it is free of
zeros of both functions. Its two logarithmic-derivative integrals are then fixed finite complex
numbers and contribute only `O(1)`. Local finiteness of the two actual divisors should provide a
common zero-free horizontal slice in every nonempty positive-height interval. This is a
source-faithful weakening of a convenience premise, not a claim that the global contour theorem
has already been proved.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01`.
- `node`: `H12-SPEISER-ADMISSIBLE-CONTOUR-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: construct cofinal common zero-free horizontal slices for `zeta` and `zeta'`;
  replace the numerical bottom-sign input by a fixed bounded bottom contribution; assemble the
  multiplicity-aware indented argument principle; prove `LevinsonMontgomeryLogCountBound` and
  `LevinsonMontgomeryCountDichotomy` for the actual counts.
- `meaningful_partial`: compile the common-slice theorem and the fixed-bottom integral bound,
  then state the first still-missing global contour/count identity exactly.
- `negative_controls`: boundary zeros, multiplicities, `t<=0`, the zeta pole at one, critical-line
  indentation, top heights crossing zeros, and the distinction between a fixed bottom constant
  and a signed bottom edge.
- `strict_boundary`: no low-zero table, numerical zero location, RH, derivative-zero exclusion,
  or unproved argument-principle theorem may enter as a premise.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
