# R1 q=2 Baez-Duarte Criterion Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-R1-BAEZ-DUARTE-QTWO-01`

## Route Audit

The preceding R5 finite-height zero-cutoff campaign is publicly closed. Its immediate height-limit
successor is not admitted: Lagarias's `A_delta` definition gives a uniformly bounded transform on a
closed strip, not vertical decay. The finite-height theorem therefore cannot be sent to infinity by
assuming decay that is absent from the source class. Distributional cutoff and regularization are a
larger campaign.

The prior R1 sparse family `(2^24)^j` is also closed. Lean proves that its target is outside the
closed span, so no candidate below reuses that normalized tuple.

## Candidate Generation And Adversarial Test

### C1: Exact natural q=1 Gram evaluation

- `statement`: Ehm's closed formula for every full natural Gram entry.
- `assumptions`: positive real scale parameters.
- `strategy`: contour shift and Muntz-series residue evaluation.
- `unresolved frontier`: asymptotic target projection residual.
- `test result`: rejected. Exact entries alone do not control inverse-Gram growth or target
  residuals, and the contour/Muntz stack is large without reducing the fixed frontier.

### C2: Modified Levinson-Selberg coefficient decomposition

- `statement`: Ehm's decompositions (50)-(55) with the modified coefficients.
- `assumptions`: explicit finite arithmetic sums.
- `strategy`: center the Landau- and Mertens-type factors and exploit their observed correlation.
- `unresolved frontier`: estimates forcing the remaining products and inversion error to zero.
- `test result`: rejected. The source calls the inversion error a major challenge and the required
  estimates very far away; numerical correlation is not an admissible premise.

### C3: q=2 Baez-Duarte convolution criterion

- `statement`: RH is equivalent to closed-span approximation after one additional Mellin factor
  `1/s`.
- `assumptions`: none beyond project definitions.
- `strategy`: convolve the existing target and positive-natural kernels with the indicator of
  `(0,1]`; use the bounded critical-line multiplier for the forward direction and an independent
  Mellin-zero obstruction for the reverse.
- `unresolved frontier`: exact L2 convolution carrier and reverse off-critical-zero estimate.
- `test result`: admitted. It is source-stated, differs from sparse coupling, and existing
  `WeilConvolution`, Fourier-Mellin, and q=1 reverse infrastructure expose a bounded engineering
  path.

### C4: Generic finite projection residual identity

- `statement`: express every finite optimal error by a Gram inverse and target pairings.
- `assumptions`: invertible finite Gram matrix.
- `strategy`: Hilbert projection and Schur complement.
- `unresolved frontier`: uniform asymptotics as the cutoff grows.
- `test result`: rejected. The identity is generic finite-dimensional algebra; compiled witnesses
  already show that Gram positivity contains no target-closure information.

### C5: Alternate sparse or lacunary subsequence

- `statement`: find a normalized subsequence with a lower frame bound and target membership.
- `assumptions`: explicit increasing natural indices.
- `strategy`: diagonal dominance plus a target-coupling estimate.
- `unresolved frontier`: target membership, which itself implies RH.
- `test result`: rejected absent new coupling evidence. The previous sparse family has an exact
  orthogonal obstruction, and changing constants would repeat the same normalized tuple.

## Selected Mathematical Proposition

Let `chi` be the indicator of `(0,1]`, let `rho_n(x) = {1/(n*x)}`, and let `*M` denote
multiplicative convolution with Haar element `dy/y`. Define

```text
h_2 = chi *M chi,
k_(2,n) = chi *M rho_n.
```

Then, in complex `L2(0,infinity)`,

```text
RiemannHypothesis iff h_2 belongs to closure(span_C {k_(2,n) : n >= 1}).
```

For `0 < Re(s) < 1`, the fixed transform identities are

```text
Mellin(h_2)(s) = 1 / s^2,
Mellin(k_(2,n))(s) = n^(-s) * (-riemannZeta(s) / s^2).
```

On `x > 1`, `h_2(x)=0` and `k_(2,n)(x)=1/(n*x)`. Hence the reverse proof retains the exact
reciprocal-moment tail rather than discarding it.

## Proposed Lean Endpoint

```lean
theorem riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_closure :
    RiemannHypothesis <->
      baezDuarteQTwoComplexTargetL2 in
        baezDuarteQTwoComplexKernelClosure
```

ASCII `in` above records the intended membership symbol; the source declaration will use Lean's
`∈` notation.

## Strength And Dependency Audit

- The endpoint is exactly RH-equivalent, not an unconditional proof of either side.
- The forward implication may reuse the compiled q=1 criterion and a bounded multiplier by `1/s`
  on the critical line.
- The reverse implication may not invert that multiplier: `|s|` is unbounded. It must prove the
  off-critical-zero obstruction directly from the q=2 physical carrier.
- No q=2 closure statement or unproved estimate may be used as a premise.
- Success has `hard_gap_delta=0`; it adds a second exact carrier whose stronger high-frequency
  downweighting may support different Gram estimates.

## Boundary And Falsification Checks

- `x=0` is excluded by the positive-half-line measure; no false total-extension convolution
  identity may be used there.
- `x>1` must produce the exact `1/(n*x)` kernel tail.
- Finite Gram positivity and finite numerical errors do not imply the closure endpoint.
- Real/complex closure equivalence must be proved or avoided, not assumed.
- Any proof that derives q=1 convergence by multiplying q=2 errors by `s` is rejected unless it
  supplies a genuine uniform high-frequency estimate.

## Campaign Stop Conditions

The campaign has at most two proof attempts after this audit. It closes locally as
`KNOWN_THEOREM_FORMALIZED` only if the exact equivalence compiles and passes the fixed verification
gate. If the convolution L2 carrier or direct zero obstruction cannot be closed in the two attempts,
record the precise missing theorem and close as `NO_PROGRESS`; do not weaken the endpoint to a
single helper merely to claim progress. The persistent RH Goal remains active in either case.
