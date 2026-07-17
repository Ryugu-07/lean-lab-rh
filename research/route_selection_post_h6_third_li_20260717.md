# Route Selection After The Theta Third-Li Campaign

Date: 2026-07-17

Previous campaign: `DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01`, publicly closed.

Next state: `ROUTE_SELECTION -> LITERATURE`.

## Authoritative frontier

- RH remains the active target.
- H6-E/G8 remains `deBruijnNewmanAllZerosReal 0`, equivalently `Lambda <= 0`.
- H6-X now contains exact positive-real information for the first three standard Li coefficients,
  but no finite prefix implies the all-index criterion.
- W2/G7 and M2/G3 remain open and RH-equivalent at their unconditional endpoints.
- The generic adjacent-gap, reverse-heat Li-transfer, and generic positive-kernel Li
  extrapolations are closed obstruction branches.

## Candidates compared

### C1: heat-family all-index Li criterion

For the exact source-normalized family

`F_t(s)=8*H_t(-i*(2*s-1))`,

define the full derivative-indexed Li family and prove, for every `t>=0`,

`AllZerosReal(H_t) <-> forall n, 0 <= Re(heatLi(t,n))`.

At `t=0`, also prove pointwise equality with the existing `liCoefficientCandidate n`.

Value: this is the first non-finite H6-X statement. It turns the open H6 threshold into an exact
all-index positivity problem and reuses the complete Hadamard/Bombieri-Lagarias spine. It does not
prove any sign unconditionally at all indices.

Decision: **SELECTED**.

### C2: re-enter the adjacent-zero dynamics attack

The previous exact law leaves a global pair remainder. No new theta-specific height-integrated
estimate is available after `OBS-H6-ADJACENT-GAP-EIGHT-01`.

Decision: defer. Re-entry without such an estimate would repeat the exhausted mechanism.

### C3: prove all zeros real at `t=1/5`

This would improve the numerical upper bound `0.22` to `0.2`, but requires certified global
nonvanishing and interval arithmetic not currently present. A single positive upper bound does not
logically reduce the sign endpoint `Lambda<=0`.

Decision: defer.

### C4: unconditional M2/G3 approximants

The exact closure criterion is already compiled and RH-equivalent. The bounded re-audit found no
new coefficient or residual estimate beyond the Wong, Carvill, sparse-Gram, and stop-audit
obstructions.

Decision: defer until a materially new approximation estimate exists.

### C5: unconditional W2/G7 positivity

The compact and fixed-width Gaussian criteria are already RH-equivalent. No new prime-side sign
mechanism survived the existing kernel-sign audits.

Decision: defer without weakening the complete positivity endpoint.

### C6: function-field Bombieri-Stepanov census continuation

The source card remains a standing census duty. The already compiled finite spectral rigidity has
no number-field finite-spectrum or uniform-tail bridge. The card does not presently unlock an
unconditional RH edge as directly as C1.

Decision: retain in the exposure/census queue.

## Strength and assumption audit

The selected statement at `t=0` is RH-equivalent. That is permitted: the campaign proves a known
criterion equivalence and does not assume either side. At `t>0` it characterizes the deformed zero
set.

The quantifier is restricted to `t>=0`. The existing project supplies an unconditional bounded
zero strip on `0<=t<=1/2` and all-real zeros for `t>=1/2`; these give the weighted reciprocal
summability needed by Bombieri-Lagarias. No corresponding all-negative-time weighted strip theorem
is currently compiled, so an all-real-time criterion would hide an unsupported hypothesis.

## Falsification and boundary screen

- A reflected one-pair model on `Re(rho)=1/2` has transformed modulus one and pair contribution
  `1-Re(q^m)>=0`.
- For the reflected off-line model `rho=1/4+i`, numerical selection finds a negative paired
  coefficient by index `99`, consistent with the Bombieri-Lagarias reverse direction. This is
  target selection only.
- A function with `F(1)=0` invalidates the local logarithm and is excluded explicitly; the actual
  heat family has `F_t(1)=8*A_t>0`.
- `H6PositiveCoshLiAudit.lean` has a negative third coefficient and therefore does not contradict
  the criterion; it warns that positive-kernel structure alone cannot prove the right-hand side.
- Output scaling by a nonzero constant must be proved Li-invariant at derivative order `n+1`, not
  assumed from informal logarithm identities.
- The affine map between an `H_t` zero and an `F_t` zero must preserve multiplicity and the exact
  line equation.

## Closest primary literature

- X.-J. Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, J. Number
  Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`.
- E. Bombieri and J. C. Lagarias, *Complements to Li's Criterion for the Riemann Hypothesis*, J.
  Number Theory 77 (1999), 274-287, DOI `10.1006/jnth.1999.2392`.
- J. C. Lagarias, *Li coefficients for automorphic L-functions*, Ann. Inst. Fourier 57 (2007),
  1689-1740, DOI `10.5802/aif.2311`.
- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function*,
  arXiv:`1904.12438`.
- B. Rodgers and T. Tao, *The de Bruijn-Newman constant is non-negative*, arXiv:`1801.05914`.

The bounded search found the general multiset Li criterion and the heat-family zero theory, but no
primary source spelling out this exact source-normalized Lean-facing heat-Li equivalence. No
novelty or priority claim is made.

## Selection

Open `LITERATURE-20260717-H6-HEAT-LI-ALL-INDEX-01`. Its indivisible endpoint is the complete
nonnegative-time equivalence and exact time-zero coefficient alignment. Generic Li helpers,
affine order lemmas, or one implication alone do not close the campaign.
