# Route Card H1: Critical-Line Zeros and Mollifiers

Date: 2026-07-17

Status: `SOURCE_ALIGNED`

## Endpoint and strength

Let `N(T)` count nontrivial zeta zeros `rho = beta + i gamma` with `0 < gamma <= T`,
including multiplicity, and let `N0(T)` count those with `beta = 1/2`. The standard RH endpoint
is not merely `N0(T) / N(T) -> 1`; it is

`forall rho, IsNontrivialZero rho -> rho.re = 1 / 2`.

Thus every critical-line proportion theorem is RH-implied partial progress. Even natural density
one permits finitely or sparsely many off-line zeros and is strictly weaker than RH in abstract
symmetric zero models.

## Sources and strongest unconditional result

- Hardy proved infinitely many critical-line zeros; Selberg proved a positive proportion.
- Levinson (1974) proved more than one third; Conrey (1989) proved more than two fifths.
- Pratt, Robles, Zaharescu, and Zeindler,
  [*More than five-twelfths of the zeros of zeta are on the critical line*](https://arxiv.org/abs/1802.10521),
  obtain a proportion slightly above `5/12`. This is the strongest unconditional proportion
  result located in the bounded source audit as of 2026-07-17.

The modern mechanism applies the argument principle to a differential combination of zeta,
multiplies by a mollifier approximating its reciprocal, and converts the resulting zero count to
twisted mean values. Longer mollifiers require new off-diagonal control; the 2018 improvement uses
long-mollifier and Kloosterman-sum input.

## First open edge and false-progress patterns

The first quantitative edge is an unconditional family of mollifier estimates that drives the
lower proportion from slightly above `5/12` to `1`. That still does not close RH: a second edge must
exclude every exceptional off-line zero, not only a density-zero set.

False-progress patterns:

- replacing a fixed positive proportion by density one and silently reading `almost all` as `all`;
- optimizing a formal mollifier functional while assuming an unproved long Dirichlet-polynomial
  mean value;
- proving a finite-height critical-line count without a certified global exclusion argument;
- treating a ratios-conjecture calculation as an unconditional mean-value theorem.

## Negative and saturation evidence

A finite or sufficiently sparse symmetric set of off-line zeros is invisible to a density-one
statement. Such a set is nevertheless detected by the compiled theorem
`exists_liCoefficientCandidate_re_neg_of_divisorZero_re_ne_half`. This is the project's sharpest
existing warning against promoting zero-proportion results to RH.

## Formalization fit

Reusable infrastructure already exists for `IsNontrivialZero`, `OnCriticalLine`, the locally
finite multiplicity function `riemannXiZeroMultiplicity`, compact finiteness, xi-zero reflection,
and all-index Li detection. Missing infrastructure includes multiplicity-weighted finite-height
counts, Riemann-von Mangoldt asymptotics, argument-principle zero counts, Dirichlet polynomials,
mollifiers, and the required twisted mean-value estimates.

## Candidate H1-B: finite count partition

**Exact proposition.** For every `T >= 0`, define the finite multiplicity-weighted counts over
`|Im rho| <= T`. Then

`N(T) = N0(T) + Noff(T)`,

where `Noff` uses `rho.re != 1/2`.

**Proposed Lean statement.** After defining a finite support cutoff:

```lean
theorem xiZeroCount_eq_critical_add_offline (T : Real) (hT : 0 <= T) :
    xiZeroCount T = xiCriticalZeroCount T + xiOfflineZeroCount T
```

**DAG and strength.** H1 counting infrastructure below H1 proportion estimates; neither implies
RH nor changes a hard gap.

**Adversarial tests.** Check `T = 0`, boundary zeros with `|Im rho| = T`, multiplicity greater than
one, and that a zero is not double-counted under reflection.

**Verdict:** `SHORTLIST_CANDIDATE`. It is source-neutral infrastructure with a finite proof surface,
but must be a separately preregistered `LITERATURE` campaign.

## Candidate H1-Q: quantitative density one

**Exact proposition.** For every integer `k >= 2`, there is `T0` such that for all `T >= T0`,

`k * N0(T) >= (k - 1) * N(T)`.

This is the explicit epsilon sequence `N0(T) / N(T) -> 1` with epsilon `1/k`.

**Proposed Lean statement.** Using the count functions from H1-B:

```lean
def CriticalLineDensityOne : Prop :=
  forall k : Nat, 2 <= k -> exists T0 : Real, forall T >= T0,
    k * xiCriticalZeroCount T >= (k - 1) * xiZeroCount T
```

**DAG and strength.** RH implies it; it is strictly weaker than RH in symmetric divisor models.
The closest unconditional result is slightly above `5/12`, not a sequence tending to one.

**Adversarial tests.** Add one off-line reflected-conjugate orbit, or one orbit at each rapidly
growing height, to an on-line model. The stated density can survive while RH fails.

**Verdict:** `OPEN_CANDIDATE`. Mathematically meaningful, but its gap from current mollifier
technology is too broad for the next proof campaign.

## Candidate H1-X: density one transfers to Li positivity

**Exact proposed implication.** `CriticalLineDensityOne -> forall n,
0 <= (liCoefficientCandidate n).re`.

**Proposed Lean statement.** A generic divisor-model version should be tested before any zeta
specialization:

```lean
-- Falsification target, not an admitted theorem.
def DensityOneImpliesLiNonnegative : Prop :=
  CriticalLineDensityOne -> forall n : Nat, 0 <= (liCoefficientCandidate n).re
```

**DAG and strength.** The conclusion is RH-equivalent in this project. The premise is weaker than
RH, so this would need a genuinely zeta-specific mechanism absent from density information alone.

**Adversarial tests.** A symmetric divisor with one real off-line orbit and an arbitrarily large
on-line population has density one. Its dominant Li transform has norm greater than one and
produces a negative coefficient. The project's compiled off-line-zero theorem confirms the same
detection principle for the actual xi divisor.

**Verdict:** `REJECTED`. Density information alone cannot support this transfer.

## Recommendation

`MONITOR` for new mollifier mean values; `FORMALIZE` only H1-B if selected for shared counting
infrastructure. Do not select H1-Q as the next direct proof attempt.
