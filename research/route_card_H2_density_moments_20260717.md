# Route Card H2: Zero Density, Moments, and Subconvexity

Date: 2026-07-17

Status: `SOURCE_ALIGNED`

## Endpoint and dependency map

For `1/2 <= sigma < 1`, let `N(sigma,T)` count nontrivial zeros with
`Re rho >= sigma` and `|Im rho| <= T`, including multiplicity. These statements have different
logical strengths and must remain separate:

- RH gives `N(sigma,T) = 0` for every `sigma > 1/2`.
- The Lindelof hypothesis is implied by RH but is not known to imply RH.
- Moment and subconvexity bounds control the size or frequency of large zeta values; they do not
  by themselves exclude one zero.
- Zero-density estimates bound the number of off-line zeros but permit a finite or sparse set.

## Sources and strongest unconditional results

- The Vinogradov-Korobov zero-free region excludes zeros near `Re s = 1`, with a boundary that
  approaches one as the height grows; it does not approach the critical line.
- Bourgain,
  [*Decoupling, exponential sums and the Riemann zeta function*](https://arxiv.org/abs/1408.5794),
  gives the critical-line subconvexity exponent `13/84` in the published result. This remains far
  from the Lindelof exponent zero.
- Guth and Maynard,
  [*New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552),
  prove the stated zero-density estimate
  `N(sigma,T) <= T^(30*(1-sigma)/13 + o(1))`. The 2026 Annals version is the strongest
  unconditional broad zero-density improvement located in this audit.

These are incomparable frontiers inside H2: pointwise size, large-value frequency, zero density,
and zero-free regions should not be collapsed into one scalar notion of progress.

## First open edges and false-progress patterns

The density-hypothesis exponent `2*(1-sigma)` remains open. Even that estimate is not RH because
it allows exceptional zeros. A path to RH needs either a zero-free statement for every
`sigma > 1/2`, or a new rigidity principle turning aggregate estimates into exclusion of a
single zero.

False-progress patterns:

- confusing a smaller density exponent with a zero-free theorem;
- treating Lindelof as RH-equivalent;
- using an asymptotic `o(1)` as a uniform explicit constant without quantifier conversion;
- transferring an estimate valid only in a subrange of `sigma` to the full critical strip;
- using numerical finite-height verification to remove the remaining infinite tail without a
  certified analytic bound.

## Formalization fit

The project already has the zeta functional equation interfaces, an unconditional `3/8`
critical-line bound, an RH-conditional reciprocal-zeta subpower bound, xi divisor finiteness, and
zero reflection. It lacks standard zero-count functions, Riemann-von Mangoldt, Littlewood/Jensen
lemmas, large-value estimates, Dirichlet-polynomial mean values, and asymptotic notation aligned
with the published zero-density theorems.

## Candidate H2-B: reflected finite-height density counts

**Exact proposition.** For `1/2 <= sigma <= 1` and `T >= 0`, let `Nge(sigma,T)` count xi zeros with
`Re rho >= sigma` and `|Im rho| <= T`, and let `Nle(sigma,T)` count those with
`Re rho <= sigma`. Then

`Nge(sigma,T) = Nle(1-sigma,T)`.

**Proposed Lean statement.** The cutoff uses absolute imaginary part so the existing map
`rho |-> 1-rho` preserves it:

```lean
theorem xiZeroCount_ge_eq_le_reflect (sigma T : Real) :
    xiZeroCountGE sigma T = xiZeroCountLE (1 - sigma) T
```

**DAG and strength.** H2 finite-count bridge from the compiled xi-divisor involution. It is known
symmetry infrastructure and does not imply a density estimate or RH.

**Adversarial tests.** Check multiplicities, `sigma = 1/2`, cutoff-boundary zeros, negative
ordinates, and the absence of double counting at the fixed line.

**Verdict:** `SHORTLIST_CANDIDATE`. It reuses strong existing infrastructure and prepares an honest
H2 statement layer.

## Candidate H2-Q: density hypothesis with explicit quantifiers

**Exact proposition.** For every `epsilon > 0` and `sigma in [1/2,1)`, there are `C,T0 > 0` such
that for every `T >= T0`,

`N(sigma,T) <= C * T^(2*(1-sigma)+epsilon)`.

**Proposed Lean statement.** After the count definition:

```lean
def RiemannZetaDensityHypothesis : Prop :=
  forall epsilon > 0, forall sigma : Real, sigma in Set.Ico (1 / 2) 1 ->
    exists C > 0, exists T0 > 0, forall T >= T0,
      xiZeroCountGE sigma T <= C * T ^ (2 * (1 - sigma) + epsilon)
```

The final Lean form must resolve coercions from natural counts and use `Real.rpow`.

**DAG and strength.** This improves the Guth-Maynard exponent `30/13` to `2`. RH implies it, but
the statement is weaker than RH and does not unlock G7 or G3 by itself.

**Adversarial tests.** Test `sigma = 1/2`, `sigma -> 1`, small `T`, positivity of the real power,
and models with a finite or logarithmically sparse off-line set.

**Verdict:** `OPEN_CANDIDATE`. It is a canonical target, not a tractable next campaign.

## Candidate H2-X: density bounds transfer to all-index Li positivity

**Exact proposed implication.** `RiemannZetaDensityHypothesis -> forall n,
0 <= (liCoefficientCandidate n).re`.

**Proposed Lean statement.** First formulate the implication for a generic symmetric genus-one
divisor and attempt a finite-orbit countermodel.

**DAG and strength.** The conclusion is RH-equivalent. Any valid proof must use structure not
present in the density hypothesis.

**Adversarial tests.** Add one off-line reflected orbit to a divisor satisfying the stated
asymptotic bound. A finite addition does not violate the large-`T` estimate, but the orbit forces a
negative Li coefficient by the dominant-transform mechanism formalized in
`LiReverseCriterion.lean`.

**Verdict:** `REJECTED`. Aggregate zero density cannot exclude a single off-line zero.

## Recommendation

`FORMALIZE` H2-B if shared finite-count infrastructure is selected. Keep H2-Q as a canonical open
benchmark and `MONITOR` the large-value literature; do not report exponent improvements as RH
closure.
