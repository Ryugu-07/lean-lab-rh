# H12 Height-Ten Left Low/Middle Phase Preregistration

Date: 2026-08-03

Campaign: `PROOF-ATTEMPT-20260803-H12-HEIGHT-TEN-LEFT-LOW-MIDDLE-PHASE-01`

Parent subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Primary mode: `LITERATURE / PROOF-ATTEMPT / HISTORICAL-OMISSION`

Status: `PREREGISTERED / DOCS-ONLY PUBLIC GATE PENDING / GLOBAL_GOAL_ACTIVE`

## Route selection

The remaining complete-boundary producers are the left low/middle vertical, the right
low/middle vertical, and the compact-middle top. This campaign selects the complete left
low/middle interval rather than another top-endpoint constant.

The left route has one structural advantage over the right route: actual zeta nonvanishing on
the positive imaginary axis is already unconditional. The right critical-line route first needs
an independent exact zero-free certificate below height `13/2`. The top route still needs a
uniform phase cover after the pointwise second-derivative checkpoint. The broader H1, H7, H10,
and H11 source frontiers currently require their recorded global moment, infinite spectral,
number-field transfer, or amplification producers. Closing a whole literal H12 boundary edge is
therefore the highest-value adjacent source attack.

## Source hinge

Levinson--Montgomery's strict half-plane argument only needs the rotated logarithmic derivative
to avoid the principal slit ray on each boundary edge. For a complex number `q`,

```text
I*q in Complex.slitPlane
```

is certified either by `q.re != 0` or by `q.im < 0`. This permits a phase handoff near the point
where the real part changes sign; it does not require one real-part sign on the entire edge.

The project already compiles:

- structural nonvanishing `riemannZeta (I*y) != 0` for every `y>0`;
- the exact zeta logarithmic-derivative reflection identity;
- second-corrected Euler--Maclaurin value and derivative centers at `1-I*y`, with explicit error
  balls;
- the complete bottom-edge slit condition at `y=0`;
- the complete left-high condition for `13/2<=y<=10`.

The omission test is whether retaining the full complex phase in the reflected finite evaluator,
rather than only its real-part upper bound, closes the entire missing interval.

## Fixed mathematical endpoint

Prove, without an external zero table or numerical premise,

```lean
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_six
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 6) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re

theorem speiserZetaDerivRatio_leftVertical_im_neg_six_thirteenHalves
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).im < 0

theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_zero_thirteenHalves
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 13 / 2) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane
```

Production declaration names may change only for elaboration or namespace reasons. The rational
split point `6` and final endpoint `13/2` are frozen.

Composing the final theorem with the already compiled high-left theorem must also produce the
complete left vertical clause on `[0,10]`.

## Proof spine

1. Derive the full complex reflection formula for `logDeriv riemannZeta (I*y)` from the existing
   functional equation, not just its real projection.
2. Generalize the reflected Euler--Maclaurin consumer from a real-part test to a complex phase
   ball. The consumer must turn exact value and derivative error balls at `1-I*y` into certified
   upper/lower bounds for the requested component at `I*y`.
3. Construct a finite rational subcover of `[0,6]` proving positive real part. Handle `y=0` by
   the existing exact bottom theorem and the positive subinterval by reflected evaluation.
4. Construct a finite rational subcover of `[6,13/2]` proving negative imaginary part.
5. Join the two phase clauses through `Complex.mem_slitPlane_iff`, then join low/middle with the
   compiled `[13/2,10]` theorem.

Finite centers may use the project's kernel-checked binary logarithm, exponential,
scaling-and-squaring, and rounded complex-power certificates. Every covering interval and every
strict margin must be a rational Lean theorem. Navigation decimals and external booleans are not
premises.

## Success and falsification

- `full_success`: all three displayed interval theorems and the complete `[0,10]` left-vertical
  clause compile and are registered with exact witnesses and selected-declaration axiom prints.
- `meaningful_partial`: the full complex reflection/phase consumer compiles and one entire frozen
  phase interval closes; the other interval is reduced to a named finite rational subcover whose
  first failed cell and exact lost margin are recorded.
- `mechanism_falsified`: a kernel-checked inequality proves that the chosen second-corrected
  center/error construction cannot separate the required component on a specified rational cell.
  The local mechanism then stops; the interval target remains open and the obstacle enters the
  hard-gap DAG.
- point values, a grid without interval transport, a moved split point, a smaller final endpoint,
  or a theorem conditional on an unproved margin do not count as full success.

## Governance and publication

Production begins only after this docs-only preregistration passes public Lean Action CI. All
production is no-sorry and no-new-axiom. Success claims require a full local build, exact
`TargetChecks`, selected-declaration `#print axioms`, a frozen implementation commit with public
CI, immutable evidence with independent public CI, and a closure receipt. RH, H12, the complete
height-ten certificate, the other right/top producers, and the global Goal remain open unless a
compiled theorem changes their status.

## Runtime

- model: Codex, GPT-5 family; exact serving variant is not exposed;
- reasoning effort: not exposed;
- numerical quota: none under V4.1;
- compaction: resumed from an inherited summary before this selection and re-read the current
  route census, door atlas, complete-boundary preregistration, active attempt log, and hard-gap
  DAG;
- global Goal: active.
