# Route Selection After Global PF4 Search

Date: 2026-07-17

Previous campaign: `FALSIFICATION-20260717-H6-XI-KERNEL-PF4-01`, publicly closed as
`NO_PROGRESS`.

Next state: `ROUTE_SELECTION -> PROOF-ATTEMPT`.

## Authoritative frontier

- RH remains the active project goal.
- H6-E/G8 is exactly `deBruijnNewmanAllZerosReal 0`.
- The all-index heat-Li criterion is compiled for every real heat time, and time zero agrees
  pointwise with the project Li coefficients.
- `deBruijnNewmanAllZerosReal (1/2)` and forward real-zero preservation are compiled.
- The first three actual-theta Li coefficients are positive, but generic positive-cosh mixtures
  can fail already at the third coefficient.
- Generic reverse-heat transfer, generic adjacent-gap continuation, PF5/PF-infinity, and the
  registered global-PF4 counterexample search are closed obstruction branches.
- W2/G7, M2/G3, H6-E/G8, and RH remain open.

## Candidates compared

### C1: actual-theta heat-Li monotonicity from negative infinite time

For every coefficient index, test whether its real part is monotone nondecreasing on `t<=0` and
tends to zero as `t` tends to negative infinity. The conjunction implies all time-zero Li
coefficients are nonnegative and therefore implies RH through the compiled all-index criterion.

The first coefficient supplies nontrivial consistency evidence: its time derivative reduces to
the ordered covariance `A*D-B*C`, whose nonnegative sign is already compiled. Higher indices have
no known sign formula and are exposed to immediate numerical and finite-model falsification.

Value: direct RH-strength attack with a sharp falsification surface and strong reuse of exact
theta moments, all-index Li definitions, and the heat equation.

Decision: **SELECTED**, subject to the mandatory conjecture gates.

### C2: unconditional fixed-width Gaussian-Weil positivity

The exact arithmetic kernel is already Lean-equivalent to RH. The individual prime kernels are
indefinite, and no new pole/archimedean/prime cancellation identity has appeared after the PF4
campaign.

Decision: defer until a concrete complete-expression sign mechanism is proposed.

### C3: direct Baez-Duarte target closure

The projection, ladder-frequency, Gram, and sparse-target audits produced no new coefficient
family or unconditional residual estimate. Restating closure membership would only rename RH.

Decision: defer without a materially new approximant.

### C4: improve the de Bruijn-Newman upper bound to `1/5`

This is a crisp open target, but it is strictly weaker than H6-E and requires a global certified
zero-exclusion computation not supplied by the new PF5 enclosure layer.

Decision: retain as a quantitative fallback, below C1 in value.

### C5: H1/H2 finite-count bridges

The multiplicity-weighted partition and reflection count identities are useful infrastructure but
do not exclude even one off-line zero. No new count-to-H6 or count-to-W2 rigidity survived the
existing sparse-orbit adversarial model.

Decision: do not select while a direct falsifiable RH-strength candidate is available.

### C6: continue global PF4 optimization

The registered random and rational-lattice domains are exhausted. Re-entry requires a materially
new analytic or optimization mechanism, not more samples.

Decision: local stop remains in force.

## Selected conjecture and strength

Write

```text
lambda_n(t) = Re(deBruijnNewmanHeatLiCoefficient t n).
```

The selected conjunction is

```text
for every n, Tendsto lambda_n atBot 0,
and for every n, lambda_n is monotone nondecreasing on (-infinity,0].
```

It implies `lambda_n(0)>=0` for every `n`, hence `deBruijnNewmanAllZerosReal 0`, hence
`Mathlib.RiemannHypothesis`. RH does not presently imply this time-monotonicity statement, so the
candidate is classified as **RH-strength or stronger**, not as a harmless bridge.

No part of the conjecture is a premise. It must first pass numerical, endpoint, finite-mixture,
and closest-literature gates. A robust counterexample is to be converted into an exact Lean
falsification theorem; a surviving numerical screen only admits a later proof attempt.

## Closest-result boundary

- Loffler, *Deformations of Xi(s)=Xi(1-s) and the heat equation*, arXiv:1510.03416, studies a
  related heat deformation but does not supply this all-index Li monotonicity statement.
- Sondow--Dumitrescu, arXiv:1005.1104, proves a different spatial modulus monotonicity of xi in
  zero-free half-planes.
- The project's exact quadratic reverse-heat countermodel shows that heat evolution and later
  critical-line zeros alone do not force earlier Li positivity. The selected conjecture therefore
  depends essentially on the actual theta weight.

No exact published match was located in the targeted primary-source search. This is not a novelty
determination, and no novelty claim is permitted.

## Selection

Open `PROOF-ATTEMPT-20260717-H6-HEAT-LI-TIME-MONOTONICITY-01`. The first stage is mandatory
falsification. Public preregistration CI must pass before numerical tooling or Lean proof-source
edits are added.
