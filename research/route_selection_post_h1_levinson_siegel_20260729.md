# Route Selection after H1 Levinson--Siegel Step Geometry Closure

Date: 2026-07-29

Status: `H7_CONNES_NESTED_PROJECTION_POSITIVE_TYPE_LOCAL_FULL_SUCCESS`

## Closed parent

Campaign `PROOF-ATTEMPT-20260729-H1-LEVINSON-SIEGEL-STEP-01` is publicly closed at
closure-receipt commit `00b731ca0686c44e899acfacea6bb51e18b8cfbb`, Lean Action run
`30410732753`, build job `90445972599`, in `1m31s`.

The closed node proves the source-admissible step geometry and its necessary steepness. It
leaves polynomial approximation, complexity-uniform mollified mean values, actual zeta counts,
H1, and RH open.

## Selection rule

Historical coverage remains an omission search. A family label is not covered until its
distinct proof mechanisms and first unavailable objects are separated. Original conjectures
and direct RH attacks remain eligible at every selection.

The next node is ranked by:

1. independent historical mechanism not yet reconstructed;
2. an exact source inference with a falsifiable negative control;
3. ability to expose the first real infinite or arithmetic producer;
4. value beyond another equivalent reformulation or numerical optimization.

## Cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H7 Connes 1998 trace formula | Formalize the nested-projection trace positivity in Theorem 5 equations `(23)`--`(25)`, and falsify it without nesting. | The project has a compact Weil criterion, finite-prime matrices, and a Berry--Keating half-line obstruction, but no independent theorem for Connes' original absorption-spectrum trace mechanism. | **Select.** |
| H10 function-field transfer | Turn finite Frobenius traces into a number-field regularized trace with uniform tails. | The finite rigidity consumer compiles, but no proposed infinite producer is yet source-valid. | Retain as a cross-route successor to the Connes trace limit. |
| H11 zero statistics | Build a statistic whose response to one off-line symmetric orbit does not vanish asymptotically. | Existing normalized statistics still permit sparse exceptions; no fixed source endpoint currently supplies absolute sensitivity. | Retain open. |
| H12 Speiser counts | Assemble the global indented argument principle and Jensen top variation. | This is a broad analytic producer after several local mechanisms, not an unmapped historical hinge. | Retain open. |
| H2 zero density | Prove the inverse Mellin line and infinite contour shift for the actual detector. | The first missing theorem is precise but remains in a recently audited family. | Retain open. |
| H14 finite verification | Formalize root isolation and Turing average bounds. | Important for finite completeness, but it cannot address the global tail without a separate theorem. | Retain open. |

## Primary-source reading

Connes 1998, Theorem 5, studies a global-field cutoff projection `Q_Lambda`. In the proof,
the transformed cutoff subspace is contained in a support-window subspace:

```text
Q'_Lambda <= S_Lambda.                                      (23)
```

The difference gives a trace distribution

```text
D_Lambda(f) = Trace((S_Lambda-Q'_Lambda) V(f)),              (24)
```

and the source concludes

```text
D_Lambda(f * f*) >= 0.                                      (25)
```

The next step is a distributional limit identifying `D_Lambda` with the Weil distribution.
The positive-characteristic theorem proves equivalence with RH for the corresponding
L-functions. The number-field program requires the archimedean/prolate cutoff and a global
trace limit.

Primary source:

- Alain Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, Theorem 5 and equations `(23)`--`(25)`:
  <https://arxiv.org/abs/math/9811068>.

Historical successors:

- Connes--Consani, *The Scaling Hamiltonian*:
  <https://arxiv.org/abs/1910.14368>.
- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*:
  <https://arxiv.org/abs/2310.18423>.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H7-CONNES-PROJECTION-DEFECT-01`.
- `node`: `H7-CONNES-NESTED-PROJECTION-POSITIVE-TYPE-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / FALSIFICATION`.
- `endpoint`: for finite complex matrices, prove that nested orthogonal projections `P,Q`
  make `H=P-Q` an orthogonal projection and identify
  `Trace(H*A*A*)` exactly with the Frobenius norm square of `H*A`; derive real nonnegativity,
  zero characterization, and the positive-type consumer.
- `negative_control`: exhibit two individual orthogonal projections and a matrix `A` for which
  the trace is strictly negative when range nesting is absent.
- `strict_boundary`: this is the finite algebraic core of source equations `(23)`--`(25)`, not
  the actual adèle-class projections, an infinite-dimensional trace-class theorem, the
  distributional limit, the Weil explicit formula, H7, or RH.
- `successor`: audit the actual number-field containment and the prolate cutoff needed to pass
  from the finite positive-type identity to a uniform trace limit.
- `production_gate`: no `LeanLab/` proof or registration edit before docs-only preregistration
  passes public CI.

The persistent RH Goal remains active.

## Local outcome

- Preregistration commit `59a6d8aa74fb48c3123e391e50e2e932408bcf66` passed Lean Action run
  `30411132179`, build job `90447227409`, in `1m33s`.
- `LeanLab/Riemann/ConnesProjectionDefect.lean` compiles the complete fixed endpoint.
- `classification`: `FULL_SUCCESS / SOURCE_POSITIVE_TYPE_HINGE_FORMALIZED`.
- The source containment is the exact finite algebraic hinge: it turns the projection
  difference into an orthogonal projection and the trace into a Frobenius norm square.
- The dimension-one negative control proves that individual orthogonal projections without
  nesting do not preserve the sign.
- This closes no actual adèle projection, trace-class, distribution-limit, Weil-positivity,
  H7, or RH edge.
- Local audit passes through the full `8793/8793` build. The next gate is frozen
  implementation public CI.
