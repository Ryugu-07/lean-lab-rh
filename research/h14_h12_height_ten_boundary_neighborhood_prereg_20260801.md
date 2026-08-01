# H14 x H12 Height-Ten Boundary Neighborhood Preregistration

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-TWO-BOUNDARY-NEIGHBORHOODS-01`

Status: `PREREGISTERED_PUBLIC_GREEN / PRODUCTION_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Exact mathematical target

At height ten, prove that the strict Speiser data hold on a positive-width real-part interval
next to each endpoint of `[0,1/2]`. Then choose cut points `a,b` with
`0<a≤b<1/2` such that proving the same data only on `[a,b]` implies the complete
`SpeiserStrictNegativeHorizontal 10` statement.

The point data are always the actual conjunction

```lean
riemannZeta (sigma + 10 * I) ≠ 0 ∧
  deriv riemannZeta (sigma + 10 * I) ≠ 0 ∧
  (speiserZetaDerivRatio (sigma + 10 * I)).re < 0
```

where inequality is propositional inequality.

## Proposed Lean outputs

```lean
theorem exists_heightTen_left_strictNegative_interval :
    ∃ a : ℝ, 0 < a ∧
      ∀ sigma : ℝ, sigma ∈ Set.Icc 0 a →
        riemannZeta (sigma + 10 * I) ≠ 0 ∧
        deriv riemannZeta (sigma + 10 * I) ≠ 0 ∧
        (speiserZetaDerivRatio (sigma + 10 * I)).re < 0

theorem exists_heightTen_right_strictNegative_interval :
    ∃ b : ℝ, b < 1 / 2 ∧
      ∀ sigma : ℝ, sigma ∈ Set.Icc b (1 / 2) →
        riemannZeta (sigma + 10 * I) ≠ 0 ∧
        deriv riemannZeta (sigma + 10 * I) ≠ 0 ∧
        (speiserZetaDerivRatio (sigma + 10 * I)).re < 0

theorem exists_heightTen_compactMiddle_reduction :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < 1 / 2 ∧
      ((∀ sigma : ℝ, sigma ∈ Set.Icc a b →
          riemannZeta (sigma + 10 * I) ≠ 0 ∧
          deriv riemannZeta (sigma + 10 * I) ≠ 0 ∧
          (speiserZetaDerivRatio (sigma + 10 * I)).re < 0) →
        SpeiserStrictNegativeHorizontal 10)
```

## Source and DAG position

Levinson--Montgomery page 52 requires strict negativity on the full height-ten horizontal. The
project already proves the left endpoint analytically for every height at least ten, while the
preceding immutable checkpoint proves the actual right endpoint through a Johansson-style
Euler--Maclaurin evaluator. This subattack joins those two source-aligned facts with openness.

The output sits strictly between the two endpoint nodes and the open full-horizontal node. It is
not equivalent to RH and does not imply RH, the height-ten certificate, or the low-zero count.

## Success and falsification criteria

Success requires all three exact actual-function outputs. The compact-middle theorem must consume
only the middle interval and the compiled endpoint neighborhoods; a theorem that merely says some
unspecified point neighborhood exists is insufficient.

The subattack is falsified if either endpoint datum does not yield an open real-parameter
neighborhood under the project's actual definitions. A type mismatch caused by totalized
division is a proof obstruction, not mathematical falsification, and must be logged separately.

## Known obstacles and nearest prior work

- `speiserZetaDerivRatio` is totalized division, so continuity must be invoked only after both
  actual nonvanishing facts are in scope.
- The endpoint-to-real-interval conversion must check the exact complex distance identity.
- The cut points must be trimmed so `0<a≤b<1/2` holds even when the two neighborhoods overlap.
- The nearest prior theorem propagates a complete strict-negative horizontal in the height
  variable. It does not propagate one point in the sigma variable or construct the middle
  reduction.

## Negative controls

- No floating-point radius or sampled value is a premise.
- No endpoint theorem is promoted directly to the full horizontal.
- No new criterion definition, custom axiom, opaque declaration, unsafe code, native decision,
  placeholder, or relaxed resource limit is allowed.
- This is a reduction of the one-dimensional top edge only. The middle interval and both
  multiplicity-bearing low-zero counts remain open.

The global RH Goal and parent campaign remain active.

## Public gate

- Preregistration commit: `13d5a8d90caad0b613aa305ffab2839552dff2e7`
- Lean Action run: `30706106727`
- Build job: `91385402460`
- Result: passed in `1m45s`
