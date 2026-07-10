# M1 Zeta Convexity Batch

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-08`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2/F1/zeta-convexity`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: stopped after boundary closure; midpoint interpolation remains open

### Fixed Final Target

The batch counts as `HARD_GAP_REDUCED` only if Lean compiles, without `sorry`, `admit`, explicit
axioms, or imported unchecked declarations, a theorem of the following strength:

```lean
∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
  ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
    C * (1 + |t|) ^ (3 / 8 : ℝ)
```

Any stronger unconditional exponent below `1/2` is also admissible. A generic strip lemma, an
edge estimate, a finite-order wrapper, or exponent arithmetic alone does not close this target.

### Source-Accurate Route

1. Use the removable entire extension of `(s - 1) * zeta(s)`.
2. Derive `zeta(1+it) = O(log(2+|t|))` from the already vendored Abel partial-sum identity with a
   truncation depending on `|t|`; convert the logarithm to a fixed `1/8` power.
3. On `Re(s)=0`, use the zeta functional equation and exact reflection identities on the special
   Gamma lines `Re(z)=1/2` and `Re(z)=1` to obtain the additional square-root loss. Thus the
   pole-removed function has boundary exponents `13/8` on the left and `9/8` on the right.
4. Formalize the midpoint case of Fiori's corrected Rademacher/Phragmen-Lindelof theorem by the
   analytic symmetrization `f(s) * conj(f(conj(1-s)))`. With `G(s)=Q+s`, its norm is monotone in
   `Re(s)` and the midpoint exponent is `(13/8 + 9/8)/2 = 11/8`.
5. Divide by `|1/2+it-1|`, which is at least `|t|`, to obtain zeta exponent `3/8`.

### Literature Audit

- Hans Rademacher, *On the Phragmen-Lindelof theorem and some applications*, Math. Z. 72
  (1959/60), 192-204, DOI `10.1007/BF01162949`.
- Andrew Fiori, *A Note on the Phragmen-Lindelof Theorem*, arXiv `2502.13282`, revised
  2026-03-22, Theorem 1 and Lemma 5; journal version JMAA 559 (2026), 130404, CC BY 4.0.
- Fiori explicitly identifies the error in the commonly cited Trudgian generalization: its
  auxiliary function depends on `Re(s)` and is not analytic. This batch will not formalize or use
  that invalid construction.
- Jean-Francois Burnol, arXiv `math/0202166`, Section 2, is the downstream consumer requiring the
  classical critical-line convexity estimate.

The inspected Fiori arXiv PDF has SHA-256
`05e6330676bcf73143992da9e0febd7cbdd235b7772129cff58a6c7e0747e06f`. The inspected arXiv source
archive is used only to recover formulas omitted by HTML rendering; no source code is involved.

### Lean Reuse Audit

- Pinned mathlib provides `PhragmenLindelof.vertical_strip` and Hadamard three-lines, but no
  polynomial-boundary zeta convexity theorem.
- `PrimeNumberTheoremAnd` commit `d963a6e694a05cd82e5f9b9ae7f4d94123e85393` is Apache-2.0. Its
  `RiemannZetaConvexity.lean` supplies only a linear strip bound, useful solely as a crude growth
  input. Its `Gamma/CriticalLineDecay.lean` proves the exact half-line Gamma norm identity needed
  for the special-line functional-equation calculation.
- `TristenHarr/thegoldenalgebra` has no declared license and leaves both the Gamma vertical-strip
  estimate and weighted Phragmen-Lindelof kernel as axioms. No code will be copied or imported.

### Assumption Frontier Before

F1 consists of the unconditional zeta convexity estimate plus the Balazard-Saias partial-sum
theorem. F2 and F3 are closed. No critical-line zeta exponent below `1/2` is currently compiled.

### Stop And Classification Rules

- `HARD_GAP_REDUCED`: the fixed final target compiles and its axiom audit contains only the normal
  Lean foundations already accepted by the project.
- `KNOWN_THEOREM_FORMALIZED`: reserved only if a source theorem is compiled but a separately
  identified mismatch prevents it from satisfying the fixed final target.
- `DEPENDENCY_GAP_IDENTIFIED`: a genuinely missing source theorem or invalid published dependency
  is isolated more sharply, with no final convexity theorem.
- `FORMALIZATION_ONLY`: only reusable infrastructure compiles and the fixed target remains
  unchanged.
- `NO_PROGRESS`: no theorem-level boundary is improved.

The batch must stop rather than insert an axiom if the Abel truncation, special Gamma ratio, crude
interior growth, or corrected midpoint interpolation cannot be closed.

### Runtime Record

- `model`: Codex, GPT-5 family; exact backend identifier not exposed
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no at preregistration
- `result_class`: `FORMALIZATION_ONLY`

## Batch Result

The fixed final `3/8` target did not compile in this batch and therefore does not count as a
hard-gap reduction. The following source-accurate prerequisites do compile without placeholder
proofs:

- the entire removable extension `zetaPoleRemoved`;
- the Abel-truncation bound `zeta(1+it) = O((1+|t|)^(1/8))`;
- the exact identity `|Gamma(1+it)|^2 = pi*t/sinh(pi*t)` away from zero;
- cancellation of the Gamma and cosine exponential factors;
- `zeta(it) = O((1+|t|)^(5/8))`;
- pole-removed boundary powers `9/8` on `Re(s)=1` and `13/8` on `Re(s)=0`.

The precise remaining subgap is the corrected Fiori midpoint symmetrization together with a
uniform interior growth witness for its weighted analytic quotient. No weighted
Phragmen-Lindelof statement was assumed.
