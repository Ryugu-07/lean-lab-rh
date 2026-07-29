# Route Selection After Hardy Complex Alpha

Date: 2026-07-29

Parent public closure: `LITERATURE-20260729-H1-HARDY-COMPLEX-ALPHA-01`

Closure receipt: `5a5bb5eb823bf4bc59f4ebb9b483a0bd6cc77408`

## Selection rule

The historical survey is an omission search. A route is ranked by the value of its next genuine
source inference, the strength of the downstream theorem it would unlock, the availability of
actual project objects, and whether a materially new repair is now visible. Ease of producing a
local Lean lemma is not a criterion.

The preceding H1 campaign creates no presumption that H1 should continue. Every live family is
reranked from its current first unavailable producer.

## Cross-family comparison

| family or subroute | first live source edge | current opportunity | decision |
| --- | --- | --- | --- |
| H1 Hardy 1914 | Differentiate equation (2) `2p` times and prove the tangential cusp limit at `alpha -> pi/2`, thereby discharging `HardyXiAbelMomentLaw`. | Equation (2), full-strip polynomial domination, and the complete conditional infinitude consumer now compile. Mathlib supplies the Jacobi theta Poisson transformation needed for a modern cusp proof. Full success would remove an explicit premise and yield Hardy's unconditional infinitely-many-critical-line-zeros theorem. | **Select.** |
| H2 classical detector | Shift the actual inverse Mellin line across the translated-zeta pole with both horizontal edges vanishing. | The inverse line and local residues compile, but the infinite rectangle and subsequent Type-I/Type-II production remain a broad package and do not alone close a density theorem. | Retain as a high-value successor. |
| H12 Levinson--Montgomery/Speiser | Assemble the global indented argument principle, Jensen top variation, and count outputs. | Local signs, indentations, zero-free slices, and winding control compile. The next edge still combines a new global count theorem with actual-zeta estimates. | Retain open. |
| H7/H8 spectral and de Branges | Construct actual adèle or Hardy-RKHS objects and prove the actual-xi positivity/trace producer. | Abstract consumers and finite algebraic hinges compile, but the concrete infinite-dimensional source objects remain unavailable. | Retain open. |
| H10 function field | Construct actual curve Riemann--Roch spaces, polar separation, intersections, and Frobenius point-count input. | Finite rigidity and the auxiliary logical gates compile; the missing producer is broad algebraic geometry rather than an isolated suppressed inference. | Retain open. |
| H11 zero statistics | Strengthen normalized pair statistics to eliminate every sparse off-line orbit. | Exact finite and moving-window identities compile, but no source theorem currently supplies the required absolute-error arithmetic amplifier. | Retain open. |
| H9 arithmetic criteria | Prove an RH-strength error estimate for Riesz, Farey, Mertens, Redheffer, or character sums. | Exact transforms compile, but each live estimate is itself RH-strength or needs a new global arithmetic argument. | Retain open. |
| H14 certified computation | Produce interval-certified zeros and a Turing completeness bound at a concrete height. | This would certify a finite rectangle and support other campaigns, but no global tail theorem would follow from it alone. | Retain as standing infrastructure. |

## Primary-source lock

The fixed source is G. H. Hardy,
*Sur les zeros de la fonction zeta(s) de Riemann*,
Comptes rendus de l'Academie des sciences 158 (1914), 1012--1014.

- equation (1):
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1014>
- equations (2)--(3), the tangential path, and the Bohr--Riesz argument:
  <https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1015>

The facsimile was checked directly. Equation (3) contains the factor `t^(2p)` in the integral.
Hardy lets `alpha` approach `pi/2` so the nome approaches `-1` tangentially and asserts that the
theta derivative term tends to zero for every `p`.

## Materially new attack angle

The previous campaign proved equation (2) by interior exponential domination and an analytic
identity theorem. It deliberately stopped before any boundary derivative.

This campaign does not merely repeat that argument and does not assume Hardy's general
Bohr--Riesz summability input. It uses the compiled two-variable Jacobi theta functional equation:

```text
tau(alpha) = I * exp(I * alpha)
sigma(alpha) = tau(alpha) + 1
tau'(alpha) = -1 / sigma(alpha).
```

For real `alpha -> pi/2` from below,

```text
Re(tau') = -1/2,
Im(tau') = (1/2) * cot((pi/2 - alpha)/2) -> +infinity.
```

Translation changes `theta3` into the alternating `theta4`; Poisson inversion changes it into a
half-integer `theta2` series at `tau'`. Its first exponent decays exponentially in
`Im(tau')`, faster than every algebraic loss from differentiation and the square-root multiplier.
The proof must establish that claim in Lean for every derivative order.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H1-HARDY-TANGENTIAL-THETA-01`.
- `node`: `H1-HARDY-TANGENTIAL-THETA-LIMIT-01`.
- `primary_mode`: `LITERATURE`.
- `full_endpoint`: prove all-order differentiation of the actual xi parameter integral, prove
  all-order tangential flatness of Hardy's exact theta term, construct
  `hardyXiAbelMomentLaw_unconditional : HardyXiAbelMomentLaw`, and compose it with the compiled
  consumer to obtain infinitely many actual critical-line nontrivial zeros.
- `strict_boundary`: no quantitative zero count, positive proportion, H1, zero-free half-plane,
  or RH.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

Original conjectures, falsification, and direct RH attacks remain open. The persistent RH Goal
remains active.

## Implementation outcome

The selected campaign reached full success. The two new no-sorry modules compile the exact
cusp-to-infinity theta transformation, all-order theta flatness, all-order actual Xi-integral
differentiation, equation (3), `hardyXiAbelMomentLaw_unconditional`, and
`infinite_criticalLineZeros_hardy`.

Frozen implementation commit `75f5c575b2c3f050f0e5703efb5ce6851d97775c` passed public Lean
Action run `30435633763`, build job `90522592740`, in `2m17s`. The campaign closes only Hardy's
qualitative critical-line infinitude theorem. Quantitative counts, positive proportion, H1, and
RH remain open; the persistent RH Goal remains active.

Docs-only immutable evidence `85f0ae62feb457961a3e71ca15db50fa195ce459` passed Lean Action
run `30436167642`, build job `90524303908`, in `2m7s`; the six frozen implementation files
remain unchanged.

Final ledger `2365765bf5ec9eb155312dce119fe6cccbbbff56` passed Lean Action run
`30436418445`, build job `90525116015`, in `1m44s`. One closure-receipt CI remains before local
STOP and fresh cross-family selection.
