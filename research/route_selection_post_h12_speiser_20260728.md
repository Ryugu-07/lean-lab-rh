# Route Selection after H12 Speiser Admissible Contour

Date: 2026-07-28

Status: `RERANK_COMPLETE / H10_WEIL_HODGE_LATTICE_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01` is publicly closed at
`MEANINGFUL_PARTIAL / SOURCE_DEPENDENCY_SPLIT`. Its final-ledger commit
`9d86466f36f872005ec270309ce09d47168d4018` passed Lean Action run `30383048725`, build job
`90355386390`, in `1m47s`.

The campaign closes the actual-divisor finite-bad-height, common zero-free horizontal,
logarithmic-derivative integrability, and fixed-bottom bounded-contribution edges. It leaves
global indentation, Jensen top variation, strict base orientation, both count conclusions,
Speiser's criterion, and RH open. Fresh cross-family selection is required.

## Cross-family comparison

| family | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H10 Weil surface/Hodge | Reconstruct the integer-divisor Hodge-index inequality and its exact Hasse--Weil point-count consumer. | The repository covers Bombieri--Stepanov and finite spectral rigidity, but not Weil's distinct surface proof. The source applies Hodge index to integral divisors `a*Gamma+b*Delta` and then reads the resulting lattice inequality as a semipositive real quadratic form. That lattice-to-real step and its spectral composition are absent. | **Select.** |
| H1 Levinson--Conrey | Construct the actual mollified mean value and the proportion-count argument. | High value, but the decisive long off-diagonal estimate remains a direct open input; optimizing another finite variational constant is not selected. | Retain open. |
| H2 density | Exclude actual slowly bending bow configurations or build a source detector that sees one exceptional zero. | The generic bow obstruction is compiled, but no source-backed zeta rigidity is presently available. | Retain open. |
| H7 spectral/Weil | Construct an infinite arithmetic operator with controlled tails and correct ground-state orientation. | Multiple finite source blocks compile; the infinite object remains broad. | Retain open. |
| H11 statistics | Upgrade pair statistics to absolute control of one sparse exceptional orbit. | The exact moving-window boundary is compiled; published density-scale errors still absorb finitely many exceptions. | Retain open. |
| H13 transfer | Transfer a proved function-field, automorphic, or nonarchimedean mechanism to the individual zeta divisor. | Existing inclusion and extra-factor audits provide no such transfer. | Monitor. |

H10 is selected for breadth, not because it is easier. The surface/Hodge proof is historically
distinct from the already formalized Bombieri--Stepanov algebra. Its exact numerical hinge can
be kernel-checked now, while the unavailable curve intersection theory remains an explicit
theorem-shaped frontier.

## Source lock

The fixed source is Kiran Kedlaya, *Two approaches to RH for curves*, Section 5.2:

`https://kskedlaya.org/weil-cohom/chapter-5.html#section-5-2-rh-via-surfaces`

For `S=X x X`, the source uses the diagonal `Delta`, the Frobenius graph `Gamma`, and the Hodge
index theorem. Applying the intersection inequality to `a*Gamma+b*Delta` yields, for integral
divisor coefficients,

```text
0 <=
  2*(a+b)*(q*a+b)
  - a^2*q*(2-2*g)
  - b^2*(2-2*g)
  - 2*a*b*N.
```

Algebraically this is

```text
2 * (g*q*a^2 + (q+1-N)*a*b + g*b^2).
```

Semipositivity forces

```text
|N-(q+1)| <= 2*g*sqrt(q).
```

The source then combines such bounds over finite-field extensions with reciprocal Frobenius
pairing to place every reciprocal zero on the critical circle. The repository already has the
finite all-power spectral consumer in `FinitePowerSumRigidity.lean`; the missing source
composition is the Hodge lattice interface.

## Omission probe

The geometric theorem naturally tests integral divisor combinations, not arbitrary real
coefficients. The campaign asks whether the exact point-count conclusion follows from the
integer lattice inequality alone, with no silently strengthened real-semipositivity premise.

The expected answer is positive because a homogeneous quadratic form nonnegative on all
integer lattice points is nonnegative on rational points by scaling and then on real points by
density and continuity. A finite lattice test is not enough and must be falsified separately.

This is a source-dependency audit. It does not claim that the actual intersection pairing,
Hodge index theorem, or curve instantiation is already in Mathlib.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H10-WEIL-HODGE-LATTICE-01`.
- `node`: `H10-WEIL-SURFACE-HODGE-LATTICE-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: integer-lattice positivity implies real positivity; real positivity gives
  the exact Hasse--Weil point-count bound; extension-wise lattice inequalities, reality of power
  sums, and reciprocal pairing feed the existing finite spectral-rigidity theorem and force the
  critical circle.
- `meaningful_partial`: the lattice-to-real theorem and exact point-count bound compile, while
  the first missing spectral composition is stated exactly.
- `negative_controls`: genus zero, positive `q`, zero coefficients, sign conventions,
  multiplicities, the `n=0` power sum, and a homogeneous quadratic form that is nonnegative on
  a fixed finite coefficient box but negative at a larger lattice point.
- `strict_boundary`: actual curve intersections, the Hodge index theorem, Riemann--Roch,
  finite-field point-count identities, a number-field transfer object, H10, and RH may not be
  inferred without compiled hypotheses.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
