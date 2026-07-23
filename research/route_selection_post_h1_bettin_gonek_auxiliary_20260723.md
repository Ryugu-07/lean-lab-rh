# Route Selection after H1 Bettin--Gonek Auxiliary

Date: 2026-07-23

Status: `H7_WEIL_POLE_BLOCK_LOCAL_COMPLETE / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Closed parent campaign

Campaign `LITERATURE-20260723-H1-BETTIN-GONEK-AUXILIARY-01` is publicly closed at
final-ledger commit `b3c967d64a7c9df3cec8c251a302190e516aad81`, Lean Action run
`29969901015`, build job `89089454873`, in `2m0s`. It closes only the removable-singularity,
auxiliary holomorphy, and selected-pole coefficient endpoint. The Mellin/contour bridge, Farmer's
moment conjecture, H1, and RH remain open.

## Cross-route comparison

| candidate | exact next object | discriminating value | verdict |
| --- | --- | --- | --- |
| D6 finite-prime Weil pole block | Instantiate the source closed-form pole matrix and prove its exact even-positive minus odd-positive rank-two decomposition. | This is the first actual arithmetic block behind the already compiled H7 Herglotz certificate. A coefficient or sign mismatch would invalidate the proposed source handoff immediately. | `SELECTED` |
| H1 Bettin--Gonek Mellin/convolution | Formalize inverse Mellin support, convolution, and contour movement after the auxiliary regularization. | Direct RH relevance and still open, but H1 has just received two consecutive mechanism-level campaigns. | `OPEN / HIGH_VALUE_SUCCESSOR` |
| D6 full arithmetic/prolate ratio | Instantiate prime, pole, archimedean, ground-vector, and prolate data and prove excess/gap convergence. | Highest endpoint value, but too broad before even one actual source block inhabits the finite matrix API. | `OPEN` |
| D10 Conrey character-sum strengthening | Attack the uniform arithmetic inequality. | Historically distinct and open, but the next exact strengthening is not yet narrower than its RH-strength endpoint. | `OPEN` |

This selection broadens the active mechanism after two H1 campaigns. It is not finite-eigenvalue
optimization and does not count one campaign as exhaustion of H1 or D6.

## Locked source formula

For `c>1`, put

```text
L = log c,
beta = L/(4*pi),
C_c = L*(sqrt c + 1/sqrt c - 2)/(2*pi^2).
```

At centered frequencies `m,n`, the source pole divided-difference matrix is

```text
Q_pole(m,n) = C_c*(beta^2-m*n)
  / ((m^2+beta^2)*(n^2+beta^2)).
```

Equivalently, with

```text
e_m = beta/(m^2+beta^2),
o_m = m/(m^2+beta^2),
```

the matrix is exactly

```text
Q_pole = C_c*(|e><e| - |o><o|).
```

Primary source: Groskin, arXiv:2607.02828, Section 2, `pole-source` and the proof of the entry
identification lemma; Connes--Consani--Moscovici, arXiv:2511.22755, Lemma 4.1. The parity-sector
interpretation is the pole decomposition audited in the June 2026 Herglotz source.

## Decision

Preregister campaign `LITERATURE-20260723-H7-WEIL-POLE-BLOCK-01`. Its fixed endpoint is the
source coefficient positivity, sample parity, closed matrix identity, rank-two decomposition,
and exact parity-sector sign law. Prime and archimedean blocks, the total Weil matrix, the
Herglotz scalar bound, simple-even ground states, source limits, and RH remain outside the
campaign and unavailable as premises.

The frozen implementation commit `4b22712b531df010901e9813710b8ad145e60392` passed public Lean
Action run `29971043533`, build job `89092937602`, in `2m30s`. The selected Lean source is frozen;
immutable evidence and final-ledger gates remain before campaign closure.
