# M1-16 Baez-Duarte Reverse Implication

Date: 2026-07-11

Fixed gap: `G2/reverse/base-criterion`.

## Sole Target

Prove the exact reverse implication of the M0-aligned published criterion:

```text
baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure
  -> Mathlib.RiemannHypothesis.
```

## Source And Route Audit

Baez-Duarte Theorem 1.1 states the equivalence between RH and closure of `chi_(0,1)` under the
positive-natural kernels `rho(1/(n*x))` in `L2(0,infinity)`. The paper obtains necessity by
inclusion in the full Beurling space and the classical Nyman-Beurling criterion.

The formal proof derives the same necessity implication directly for the already aligned carrier.
This does not assert the general base criterion. The direct proof uses the classical Mellin zero
obstruction and the source-specific tail structure already compiled during M0.

## Compiled Argument

1. Prove every finite natural-kernel sum has zero full Mellin transform at a zeta zero in the
   open critical strip, using `hasMellin_baezDuarteKernel`.
2. Prove the local weight `x^(s-1)` belongs to `L2(0,1)` when `Re(s)>1/2`, and apply Bochner
   Holder to the local approximation error.
3. Compute the target integral on `(0,1)` as `1/s`.
4. Use the exact source tail `m/x` to compute the `(1,infinity)` integral as `m/(1-s)`.
5. Split the zero full Mellin transform at one, obtaining

   ```text
   localErrorMellin = 1/s + m/(1-s).
   ```

6. From `fullLineError = unitIntervalError + m^2`, choose an approximant small enough that both
   the Holder term and moment term are strictly smaller than `norm(1/s)`, a contradiction.
7. Exclude all zeta zeros with `1/2<Re(s)<1`. Reflect a nontrivial zero left of the critical line
   with `completedRiemannZeta_one_sub`; the reflected zero is either in that open strip or in the
   already zero-free half-plane `Re(s)>=1`.
8. Apply the existing exact equivalence between the project nontrivial-zero predicate and
   `Mathlib.RiemannHypothesis`.

## Result

- `riemannZeta_ne_zero_of_baezDuarteComplexTarget_mem_closure` compiles the right-half-strip zero
  obstruction.
- `baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis` compiles the sole target.
- No Nyman-Beurling criterion, half-plane Hardy-space theorem, or new axiom is assumed.

`result_class`: `HARD_GAP_REDUCED`.

This removes only the reverse implication of the aligned natural-kernel criterion. The remaining
M1/G2 frontier is the actual forward convergence assembly `RH -> closure`; the existence of
separate F1/F2/F3 estimates is not itself that theorem. M1, G1, D, and RH remain unproved.

Full `lake build` passes with 8605 jobs. Incomplete-proof and explicit-declaration scans over
`LeanLab` and `PrimeNumberTheoremAnd` have no matches, and `git diff --check` passes. The two main
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Public CI is recorded after
the batch commit is pushed: commit `e17c7e7` passes Lean Action CI run `29152779507`, job
`86544889780`, in 2m9s.
