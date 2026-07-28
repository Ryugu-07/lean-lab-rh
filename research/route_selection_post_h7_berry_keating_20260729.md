# Route Selection after H7 Berry--Keating Half-Line Closure

Date: 2026-07-29

Status: `H1_LEVINSON_SIEGEL_STEP_GEOMETRY_SELECTED`

## Closed parent

Campaign `FALSIFICATION-20260729-H7-BERRY-KEATING-HALFLINE-01` is publicly closed at
closure-receipt commit `9a545be84ea2bd053936195f5e616f92ee6730b6`, Lean Action run
`30408587106`, build job `90439516550`, in `1m34s`.

The closed theorem says that every standard Berry--Keating half-line mode has squared density
`1/x` and is not in the relevant `L2` space. It does not close the full operator theorem,
compact-graph Weyl obstruction, global arithmetic confinement, H7, or RH.

## Selection rule

Historical coverage is an omission search. A route is not covered merely because its family
label has appeared. The next target is ranked by:

1. whether a representative historical mechanism remains unreconstructed;
2. whether a primary source exposes a precise overlooked freedom or hidden loss;
3. whether Lean can distinguish a genuine bridge from a cosmetic optimization;
4. whether the result identifies the next analytic producer or a route obstruction.

Direct RH attacks and original conjectures remain eligible at every selection.

## Cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1 Levinson--Conrey and Siegel | Separate short-mollifier length from the growing complexity of the auxiliary derivative combination by auditing the source symmetry class and its step-function limit. | The repository proves a variational sufficiency theorem but has not reconstructed the source's structural explanation for why arbitrarily short mollifiers can work. The 2025 source explicitly overturns a long-held negative expectation and connects the optimizer to Siegel's function. | **Select.** |
| H7 Connes trace/NCG | Construct the semilocal or global trace object and isolate the exact positivity/limit gap. | Historically central, but the full adele-class producer is broader than the bounded H1 structural endpoint. | Retain as a leading successor. |
| H10 function-field transfer | Replace finite Frobenius traces by a source-valid number-field regularized trace. | The finite mechanisms and ordinary-trace obstruction are mapped; no concrete replacement producer is fixed. | Retain open. |
| H11 Montgomery statistics | Derive an absolute last-exception-sensitive statistic rather than a normalized density conclusion. | Existing theorems still absorb a finite or density-zero off-line orbit. | Retain open. |
| H12 Speiser counts | Assemble the global indented argument principle and top Jensen variation. | Several local inputs compile, but the next edge is a broad global count theorem. | Retain open. |
| H2 zero density | Complete the inverse Mellin detector and arithmetic Type-I/Type-II estimates. | The first missing edge is an analytic producer, not an unaudited bounded inference. | Retain open. |

## Primary-source reading

Conrey's 1989 paper uses a general differential combination of zeta, the argument principle,
Littlewood's lemma, and a mollifier. Its equations `(32)`--`(39)` convert an auxiliary right-zero
count and a mollified second moment into a lower bound for critical-line zeros.

The 2025 Conrey--Farmer--Kwan--Lin--Turnage-Butterbaugh paper makes a sharper structural
observation. Its admissible derivative-combination functions satisfy

```text
Q(0) = 1
Q(y) + Q(1-y) = 1
```

on `[0,1]`. The source constructs optimizers depending on the mollifier length and proves that,
as the length tends to zero, they converge pointwise to the discontinuous Siegel step:

```text
1       for y < 1/2
1/2     for y = 1/2
0       for y > 1/2.
```

Thus the historically missed freedom is not a decimal improvement. The auxiliary derivative
combination becomes increasingly sharp as the mollifier becomes short.

Sources:

- <https://aimath.org/~kaur/publications/24.pdf>
- <https://arxiv.org/abs/2508.11108>

## Omission probe

This campaign does not attempt to reprove the source hypergeometric optimizer. It asks a prior
structural question:

```text
Does the exact source symmetry class itself permit smooth step approximation,
and is unbounded transition steepness unavoidable?
```

An explicit normalized logistic family will test existence. A general mean-value theorem will
test necessity. Success separates two barriers that have often been conflated:

1. short mollifier length is not by itself a structural obstruction;
2. uniform low-complexity or uniformly bounded-slope auxiliary combinations cannot approach
   the Siegel step.

## Fixed next campaign

- `campaign`: `PROOF-ATTEMPT-20260729-H1-LEVINSON-SIEGEL-STEP-01`.
- `node`: `H1-LEVINSON-SIEGEL-STEP-GEOMETRY-01`.
- `mode`: `PROOF-ATTEMPT / HISTORICAL_OMISSION / CROSS_ROUTE`.
- `endpoint`: construct a smooth normalized logistic family satisfying the source endpoint and
  reflection identities; prove its exact three-case pointwise limit to the Siegel step; prove
  explicit midpoint-slope growth; and prove a general mean-value lower bound showing that every
  sharp transition requires a large derivative somewhere.
- `negative_controls`: do not identify the logistic family with the source optimizer; do not
  replace pointwise convergence by uniform convergence; do not infer polynomial degree bounds
  from derivative bounds; do not import a mollified mean-value theorem.
- `successor`: compare the explicit family with the source energy and then reconstruct the
  Levinson argument-principle/Littlewood counting bridge at the actual zeta auxiliary.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
