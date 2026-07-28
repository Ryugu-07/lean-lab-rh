# H2 Classical Zero-Detector Mellin Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01`

Node: `H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `MEANINGFUL_MELLIN_PARTIAL / IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Source statement

Maynard--Pratt Appendix C reconstructs the classical zero detector as follows. For a cutoff `M`,
define

```text
M_M(s) = sum_{m <= M} mu(m) / m^s,
a_M(n) = sum_{m | n, m <= M} mu(m).
```

Then `a_M(1)=1` and `a_M(n)=0` for `2 <= n <= M`. For `Y>0`, form

```text
I(z) = sum_{n >= 1} a_M(n) * n^(-z) * exp(-n/Y).
```

Mellin inversion gives an original-line representation with
`Y^w * Gamma(w) * M_M(z+w) * zeta(z+w)`. At an actual zeta zero `z=rho`, shifting to
`Re(w)=1/2-Re(rho)` crosses the zeta pole at `w=1-rho`. The Gamma pole at `w=0` is canceled by
`zeta(rho)=0`. Comparing the shifted expression with the coefficient gap gives the
dyadic-block versus line-remainder detector.

## Exact fixed endpoint

The production campaign must attempt the following in order, without `sorry`.

1. Define a finite-cutoff Mobius arithmetic function and its Dirichlet convolution with the
   arithmetic zeta function.
2. Prove the coefficient formula

   ```text
   a_M(n) = sum_{d | n, d <= M} mu(d).
   ```

3. Prove `a_M(1)=1` for `1 <= M`, and `a_M(n)=0` for `2 <= n <= M`. Record every positivity and
   cutoff assumption explicitly.
4. Prove absolute L-series summability for `Re(s)>1` and the actual product identity

   ```text
   L(a_M,s) = M_M(s) * riemannZeta(s).
   ```

   The finite mollifier factor must be the project's actual Mobius Dirichlet polynomial.
5. Define the exponentially smoothed series `I(z;M,Y)` for `Y>0`, prove summability in the
   source half-plane, and isolate its `n=1`, coefficient-gap, dyadic-block, and tail terms.
6. Prove the original-line Gamma--Mellin representation on a source-valid vertical line, with
   all sum/integral exchanges justified.
7. For an actual `IsNontrivialZero rho` with `1/2 < rho.re`, shift to
   `Re(w)=1/2-rho.re`. Prove that the Gamma pole at zero is removable after multiplication by
   `zeta(rho+w)`, identify the zeta pole residue at `w=1-rho`, and discharge the horizontal-edge
   limits using explicit Gamma decay and available zeta growth bounds.
8. Derive the exact shifted detector identity and a finite, cardinality-audited theorem:
   either the shifted-line remainder is large or one nonempty dyadic block is large. The
   threshold must depend on the actual number of blocks; no informal `O(log T)` may enter a Lean
   theorem.
9. Package the result in an aggregate certificate that keeps analytic identities, finite
   detector algebra, and later counting estimates as separate fields.
10. Compile a cardinality negative control: without a bound on the number of blocks, a fixed
    total mass can be split into arbitrarily small individual blocks. This prevents promotion of
    a large total sum to a uniform block threshold.

Exact declaration names may follow local style. The contour variable must not be confused with
the zeta-zero variable. Every use of a zero must go through the project's actual
`IsNontrivialZero` predicate.

## Success criteria

`FULL_MELLIN_SHIFT_DETECTOR_SUCCESS` requires all ten clauses, a proven Target, an exact open
successor Target, exact TargetChecks, selected transitive axiom prints with standard axioms only,
empty forbidden scans, warning-as-error compilation, a full build, and every public CI gate.

`MEANINGFUL_MELLIN_PARTIAL` requires clauses 1--5, 8's abstract finite detector theorem, and
clause 10. The first unavailable original-line Mellin inversion, meromorphic contour-shift,
residue, or horizontal-edge theorem must be recorded exactly rather than replaced by an
assumption registered as proved.

`FALSIFIED` applies if the stated coefficient gap or the cardinality-audited detector implication
is false. A minimal counterexample and the corrected statement must be compiled.

## Negative controls and claim boundary

- `CUTOFF_POSITIVITY`: `M=0` does not give `a_M(1)=1`.
- `COEFFICIENT_GAP`: cancellation through `n<=M` uses the full divisor set; it is invalid for
  `n>M`.
- `PRODUCT_ZERO`: a zero of `M_M(s)*zeta(s)` need not be a zeta zero because the finite mollifier
  can vanish.
- `GAMMA_POLE`: the pole at `w=0` is canceled only after specializing to an actual zeta zero.
- `ZETA_POLE`: the residue at `w=1-rho` is retained; it is not silently discarded as an error.
- `SHIFT_WINDOW`: the target line lies between `-1/2` and `0` only under the audited real-part
  conditions; farther Gamma poles must not be crossed.
- `DYADIC_CARDINALITY`: the individual-block threshold depends on a proved finite block count.
- `NO_COUNT_PROMOTION`: one detector dichotomy does not count Type-I or Type-II zeros.
- `NO_DENSITY_PROMOTION`: even a sharp density estimate permits finite or sparse exceptions.
- `NO_RH`: H2 and RH remain open.

Expected classification:

- `historical_subroute_coverage_delta=1`;
- `classical_zero_detector_delta=1` only under full success;
- `mobius_coefficient_gap_delta=1`;
- `mellin_shift_delta=1` only if the actual shift compiles;
- `zero_density_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source, Target, TargetCheck, axiom-audit entry, or aggregate import may be
created or edited until this docs-only preregistration passes public Lean Action CI.

The persistent RH Goal remains active. Local completion returns to fresh historical route
selection after the full evidence chain.

## Implementation result

The docs-only preregistration commit
`fc6e3c1ac5a8effc4db842716078229c869f6f56` passed public Lean Action run
`30391792808`, job `90384919913`, in `2m0s` before production edits.

The production module now compiles clauses 1--5, the source-independent finite theorem from
clause 8, and clause 10. It additionally compiles the complete forward Mellin transform and the
two local singularity calculations required by clause 7:

- `Gamma(w)*zeta(rho+w)` has a differentiable `dslope` replacement at `w=0` for every actual
  `IsNontrivialZero rho`;
- the translated zeta pole at `w=1-rho` has the exact retained residue
  `Y^(1-rho)*Gamma(1-rho)*M_M(1)`.

The first unavailable theorem is the vertical inverse identity
`ClassicalDetectorInverseMellinLine`. Therefore the infinite rectangle shift, horizontal-edge
limits, shifted detector identity, Type-I/Type-II counts, density estimates, H2, and RH remain
open. The accepted classification is `MEANINGFUL_MELLIN_PARTIAL`, not full success.

The frozen implementation commit `b050e9d027ca0fa27619803df1e764b1a65f887c` passed public Lean
Action run `30394320528`, job `90393394704`, in `2m37s`. Proof sources remain frozen while
docs-only immutable evidence is published.

Immutable evidence `ee2e2adbadad66ed8927b3aae62bd7c49f1f9baa` passed public Lean Action
run `30394609125`, job `90394329560`, in `1m41s`; its `LeanLab/` diff from the frozen
implementation is empty. One docs-only final-ledger gate remains before returning to fresh
historical route selection.
