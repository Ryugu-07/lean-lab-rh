# H1 Hardy--Littlewood Eta Primitive Mean Square Preregistration

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTRATION_LOCAL / PUBLIC_CI_PENDING`

## Parent and fixed source

- `parent_closure`: H1 eta-remainder receipt
  `5bce854bcfbcb30b8f27c1ff629d6311792c5614`, public run `30496464584`, build job
  `90726356672`, passed in `1m45s`.
- `primary_source`: G. H. Hardy and J. E. Littlewood,
  *The zeros of Riemann's Zeta-Function on the critical line*,
  Mathematische Zeitschrift 10 (1921), pages 287--288:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.
- `source_sha256`:
  `050b62cc3ed048e335d27bb93804340c03f70f94d2f5a1f7f6e95873647312ec`.
- `compiled_left_context`:
  `LeanLab/Riemann/HardyLittlewoodEtaRemainder.lean` and
  `LeanLab/Riemann/HardyLittlewoodEtaAbelTransfer.lean`.
- `compiled_finite_producer`:
  `LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean`.
- `compiled_right_consumer`:
  `LeanLab/Riemann/HardyLittlewoodSourceNormalization.lean` and
  `LeanLab/Riemann/HardyLittlewoodLinearCount.lean`.
- `first_open_obstacle`:
  `OBS-H1-HARDY-LITTLEWOOD-ETA-ERROR-MEAN-SQUARE-01`.

## Source statement and premise minimization

Hardy--Littlewood Lemma 7 defines

```text
psi(t) = sum_(n>=2) (-1)^(n-1) * n^(-1/2-i*t) / log(n)
```

and states

```text
integral_(T to 2T) |psi(t+u)|^2 dt = O(T)
```

uniformly for `0<=u<=T`. Lemma 8 proves a full mean-square asymptotic. The current project
consumer only needs an explicit upper bound for the eta-window error. Full asymptotic
evaluation and the source's stronger `O(N/log N)` finite off-diagonal estimate are therefore
not full-success requirements.

## Proposed Lean surface

Equivalent names and explicit constants are allowed. The public interface should include:

```lean
def hardyLittlewoodThetaSeriesValue (s : ℂ) : ℂ :=
  Filter.limUnder Filter.atTop
    (fun N => hardyLittlewoodThetaPartialSum s N)

theorem hardyLittlewoodEtaPrimitive_eq_thetaSeriesValue (t : ℝ) :
    hardyLittlewoodEtaPrimitive t =
      -(hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
          hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint 0)).im

theorem integral_normSq_hardyLittlewoodThetaSeriesValue_shift_le
    {T u : ℝ} (hT : 1 ≤ T) (hu0 : 0 ≤ u) (huT : u ≤ T) :
    (∫ t in T..2*T,
      Complex.normSq
        (hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u)))) ≤
      hardyLittlewoodThetaMeanSquareConstant * T

theorem lintegral_hardyLittlewoodEtaWindowError_sq_le
    {T H : ℝ} (hT : 1 ≤ T) (hH0 : 0 ≤ H) (hHT : H ≤ T) :
    (∫⁻ t, ENNReal.ofReal (|hardyLittlewoodEtaWindowError H t| ^ 2)
      ∂(volume.restrict (Set.Icc T (2*T)))) ≤
        ENNReal.ofReal
          (hardyLittlewoodEtaWindowMomentConstant * T)
```

The constants must be explicit project definitions, nonnegative, and independent of
`T`, `u`, and `H` in the stated regime.

## Required proof chain

1. Define the canonical ordered Theta-series value using the existing literal partial sums.
2. Prove ordered convergence and the explicit critical-line remainder from the public eta
   remainder plus the compiled eta-to-Theta transfer.
3. Prove exact equality between the critical-line partial sum and
   `hardyLittlewoodThetaPolynomial`.
4. Prove the finite primitive identity with the correct sign and the `n=1` cancellation.
5. Pass the finite identity to the ordered limits without assuming termwise differentiation of
   the infinite series.
6. Choose one explicit natural cutoff uniformly for
   `t in [T,2T]`, `0<=u<=T`, with all real-to-natural rounding checked.
7. Combine the finite `O(L+N)` theorem and the explicit Theta tail to prove the shifted source
   mean square `Cpsi*T`.
8. Use the primitive identity at shifts `0` and `H` to prove the eta-window-error square
   moment uniformly for `0<=H<=T`.
9. Convert the interval integral into the exact restricted-measure `lintegral` premise used by
   `hardyLittlewood_source_finite_count`.
10. Register one proven H1 Target, exact TargetChecks, selected axiom prints, and the root import.

The proof may use a different but definitionally aligned canonical value or integration route.
It may not assume the source infinite-series identity or mean-square estimate.

## Full-success criteria

`FULL_SUCCESS` requires all ten proof-chain items, explicit uniform constants, and the exact
restricted-measure consumer theorem. It also requires no placeholders, warning-as-error
compiles, exact checks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, a full build, and independent public CI.

## Meaningful partial, falsification, and hard gap

`MEANINGFUL_PARTIAL` requires:

- canonical ordered `psi` with an explicit critical-line remainder;
- exact finite-polynomial alignment;
- the primitive identity, or a compiled reduction of that identity to one exact
  uniform-integral limit theorem;
- the shifted infinite mean square, or a compiled reduction to one exact cutoff/tail
  inequality.

`FALSIFIED_STATEMENT` applies if Lean finds the displayed primitive sign, polynomial alignment,
uniform shift regime, or proposed constant form false. The corrected statement and a compiled
counterexample or contradiction must be recorded.

`HARD_GAP_REDUCED` applies only if all finite identities and uniform tails compile and one exact
measure/integration theorem remains unavailable. Tactic friction is not a hard gap.

## Negative controls and claim boundary

- Pointwise Theta convergence does not imply the source mean-square bound.
- The finite polynomial theorem cannot be applied with an infinite cutoff.
- An estimate only for `u=0` does not directly control the window error at arbitrary
  `0<=H<=T`.
- Assuming the equality between the integral primitive and the source series is not full
  success.
- A constant depending on `T`, `u`, `H`, or the chosen cutoff is not source-uniform.
- Reproving Lemma 8's exact asymptotic is unnecessary once an explicit upper bound feeds the
  count consumer.
- Improving the eta remainder constant `4` is outside scope.
- No source-X moving-window moment, parameter budget, unconditional linear count, H1, or RH is
  claimed.

## Audit and publication gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. warning-as-error compile of the new module and registration files;
4. exact TargetChecks and selected standard-only axiom prints;
5. empty forbidden/resource scans;
6. `git diff --check` and full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop only this local campaign and rerank
all historical families.
