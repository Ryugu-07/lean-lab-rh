# Census Batch A: Nine-Candidate Audit

Date: 2026-07-17

Classification: `ROUTE_CENSUS`

This audit covers H1, H2, and H6 under
[`next_route_census_instruction_20260716.md`](next_route_census_instruction_20260716.md). No
candidate below is a Lean premise. `SHORTLIST_CANDIDATE` means only that a separate campaign may
be preregistered to test it.

## Verdict table

| id | kind | exact endpoint | relation to RH | verdict | reason |
| --- | --- | --- | --- | --- | --- |
| H1-B | bridge | `N = N0 + Noff` for every finite-height multiplicity cutoff | infrastructure below RH | `SHORTLIST_CANDIDATE` | Finite, source-neutral count layer using the compiled xi divisor. |
| H1-Q | quantitative | `k*N0(T) >= (k-1)*N(T)` eventually for every `k>=2` | RH-implied, strictly weaker in divisor models | `OPEN_CANDIDATE` | Canonical density-one target, but far beyond the current `>5/12` frontier and still insufficient for RH. |
| H1-X | cross H1-H4 | density one implies all Li coefficients nonnegative | conclusion is RH-equivalent | `REJECTED` | One sparse off-line orbit preserves density one but triggers Li negativity. |
| H2-B | bridge | `Nge(sigma,T)=Nle(1-sigma,T)` | symmetry infrastructure | `SHORTLIST_CANDIDATE` | Exact finite-count consequence of xi reflection. |
| H2-Q | quantitative | density exponent `2*(1-sigma)+epsilon` | RH-implied, weaker than RH | `OPEN_CANDIDATE` | Canonical density hypothesis; does not exclude an exceptional zero. |
| H2-X | cross H2-H4 | density hypothesis implies all Li coefficients nonnegative | conclusion is RH-equivalent | `REJECTED` | Any finite off-line orbit survives an asymptotic density bound and defeats the conclusion. |
| H6-B | bridge | `H_0(z)=(1/8)xi((1+iz)/2)` | exact definition bridge to RH | `SHORTLIST_CANDIDATE` | Bounded M0-style task and prerequisite for every honest H6 campaign. |
| H6-Q | quantitative | all zeros of `H_(1/5)` are real | gives `Lambda<=0.2`, weaker than RH | `OPEN_CANDIDATE` | Crisp improvement over `0.22`, but analytically and computationally large. |
| H6-X | cross H6-H4 | all-real zeros of `H_t` iff heat-Li coefficients are nonnegative | RH-equivalent at `t=0` | `SHORTLIST_CANDIDATE` | Reuses compiled Li infrastructure after exact heat-family alignment; analytic hypotheses must remain explicit. |

## Three-delta accounting

- `rh_frontier_delta = 0`
- `route_infrastructure_delta = 0`
- `engineering_delta = 0`

No Lean declaration was added, no candidate passed proof status, and no RH progress is claimed.

## Route recommendation

Among Batch A candidates, H6-B has the best combination of exact source endpoint, reuse of current
xi/Fourier infrastructure, and useful failure information. It should be value-ranked against
direct W2/G7, M2/G3, and RH attacks in `ROUTE_SELECTION`; it has no automatic priority.

For Census Batch B, build the required H10 Bombieri-Stepanov/function-field route card. Its goal is
to isolate the finite-field ingredient that forces the critical line and state the exact
number-field transfer gap, not to import analogy as a premise.
