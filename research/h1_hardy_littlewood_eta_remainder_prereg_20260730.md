# H1 Hardy--Littlewood Eta Remainder Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `FULL_SUCCESS / FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_CI_PENDING`

Public preregistration gate: commit `5402fc312747bf68a0bedcdd6e67b8dd71241ed2`,
Lean Action run `30492875305`, build job `90714768715`, passed in `1m53s`.

## Parent and fixed source

- `parent_closure`: H2 classical detector dyadic-dichotomy receipt
  `d85a370e4adaffdcf51e86fa8b38ff459518d491`, public run `30492021514`, build job
  `90711944691`, passed in `1m38s`.
- `primary_source`: G. H. Hardy and J. E. Littlewood,
  *The zeros of Riemann's Zeta-Function on the critical line*,
  Mathematische Zeitschrift 10 (1921), pages 284--286:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.
- `source_sha256`:
  `050b62cc3ed048e335d27bb93804340c03f70f94d2f5a1f7f6e95873647312ec`.
- `compiled_left_context`:
  `LeanLab/Riemann/HardyLittlewoodSourceNormalization.lean`.
- `compiled_right_context`:
  `LeanLab/Riemann/HardyLittlewoodEtaAbelTransfer.lean` and
  `LeanLab/Riemann/HardyLittlewoodFiniteMeanSquare.lean`.
- `first_open_obstacle`: `OBS-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`.

## Source statement

Hardy--Littlewood Lemma 3 states that there is a sufficiently small positive constant `A`
such that, uniformly for `sigma>=sigma0>0` and `abs(t)<A*x`,

```text
(1-2^(1-s))*zeta(s)
  = sum_(n<=x) (-1)^(n-1)*n^(-s) + O(x^(-sigma)).
```

The source derives this from Lemma 2 at `x` and `x/2`; the two
`x^(1-s)/(1-s)` terms cancel exactly. The endpoint may choose a fixed source-valid constant
such as `A=1`. Maximizing `A` is outside scope.

## Fixed proof candidate

For the unit phase of the actual alternating term, use the exact consecutive ratio

```text
q_n = -exp(-i*t*log((n+1)/n)).
```

The proposed finite mechanism is:

1. `q_n` is close to `-1` when `abs(t)<=N<=n`;
2. `1-q_n` is therefore uniformly separated from zero;
3. with `c_n=(1-q_n)^(-1)`,
   `u_n=c_n*(u_n-u_(n+1))`;
4. finite summation by parts bounds a phase block by two endpoint coefficients plus the total
   variation of `c_n`;
5. the exponential chord inequality and monotonic logarithmic increments make that variation
   telescope;
6. Abel summation against the decreasing amplitude `n^(-sigma)` gives the eta remainder.

Equivalent finite formulations are allowed. No part of this candidate is accepted until Lean
compiles it.

## Required definitions

The implementation should define, or provide equivalent reusable definitions for:

1. the actual unit logarithmic phase and its consecutive ratio;
2. the inverse-difference coefficient `(1-q_n)^(-1)`;
3. finite shifted phase blocks and the corresponding power-weighted blocks;
4. a canonical ordered eta-series value on `0<re(s)`;
5. an aggregate certificate exposing the phase bound, eta remainder, actual eta
   identification, and Theta transfer.

The existing literal `hardyLittlewoodEtaSourceTerm`,
`hardyLittlewoodEtaPartialSum`, and `hardyLittlewoodEta` definitions must be reused at the
public interface.

## Full-success criteria

`FULL_SUCCESS` requires all of the following:

1. Prove the exact unit-phase factorization of
   `hardyLittlewoodEtaSourceTerm (sigma+t*I) n` for every `n>=1`.
2. Prove the exact consecutive-ratio identity for the actual logarithmic phase.
3. Under a fixed explicit source-valid regime such as `abs(t)<=N<=n`, prove uniform
   separation of `1-q_n` from zero and an explicit norm bound for its inverse.
4. Prove a finite total-variation estimate for the inverse-difference coefficients using
   actual logarithmic increments. An assumed variation bound is insufficient.
5. Prove an explicit constant `B` such that every actual shifted unit-phase block beginning
   after `N` has norm at most `B`, uniformly in its length.
6. For every `sigma>0`, prove the decreasing-power Abel estimate and obtain a literal
   `C*N^(-sigma)` bound for every actual eta block in the same source regime. No
   `abs(s)` factor may remain.
7. Construct the ordered eta-series value, prove convergence, and prove the explicit uniform
   remainder for every natural cutoff after the source threshold.
8. Prove that this ordered value equals
   `hardyLittlewoodEta s=(1-2^(1-s))*riemannZeta s` for `0<re(s)` and `s!=1`.
   A locally uniform analytic-limit and identity-theorem proof is allowed.
9. Specialize the result to the actual critical line and compose it with
   `exists_hardyLittlewoodThetaValue_of_etaRemainder`.
10. Register one H1 Target as proven, add exact TargetChecks, selected axiom prints, and the
    project-root import.

The final constant may be larger than the exploratory value `3`; it must be explicit,
uniform, and independent of `t`, `N`, and block length in the stated regime.

## Local implementation result

All ten full-success mathematical criteria now compile in
`LeanLab/Riemann/HardyLittlewoodEtaRemainder.lean`.

- The actual unit phases have the exact consecutive ratio
  `-exp(-i*t*log((n+1)/n))`.
- In the source regime `1<=N` and `abs(t)<=N`, the inverse-difference denominator has norm at
  least one, its inverse has norm at most one, and the total inverse-coefficient variation is
  at most one.
- Every actual unit-phase block after `N` has norm at most `4`.
- Every actual eta block after `N` has norm at most `4*N^(-sigma)` for `sigma>0`, with no
  `abs(s)` factor.
- The naturally ordered partial sums are Cauchy and converge locally uniformly on
  `re(s)>0`; their canonical `limUnder atTop` value has the same explicit remainder.
- Odd/even splitting identifies that value with
  `(1-2^(1-s))*riemannZeta s` for `re(s)>1`, and the identity theorem extends the equality to
  `re(s)>0`, `s!=1`.
- The resulting project-eta remainder, critical-line specialization, and composition with
  `exists_hardyLittlewoodThetaValue_of_etaRemainder` compile.

Local classification: `FULL_SUCCESS / HARDY_LITTLEWOOD_LEMMA3_FORMALIZED`.

Registration and local audit are green:

- 1181-line production module;
- one proven Target and nine exact TargetChecks;
- nine selected axiom prints, each exactly
  `[propext, Classical.choice, Quot.sound]`;
- warning-as-error compiles for the production module, all registration files, and root import;
- empty forbidden/resource scans and `git diff --check`;
- full build `8805/8805`.

Frozen implementation commit `e3341491b34959f2b1eb5d4e1fe2f6fc6cb6ac6f` passed independent
Lean Action run `30495767931`, build job `90724079010`, in `2m17s`. The five proof and
registration files are frozen and have an empty diff from that commit. At implementation
publication, immutable-evidence CI, final-ledger CI, and closure-receipt CI remained required.

Docs-only immutable-evidence commit `4994f8bf406f252ed5f6de467cab30faa2254497`
passed Lean Action run `30496035652`, build job `90724980466`, in `1m33s`. The frozen
five-file diff remains empty.

Docs-only final-ledger commit `777a291700131dfbb157017398cf0d6115f61ebc` passed Lean Action
run `30496233624`, build job `90725622666`, in `1m38s`; the frozen diff remains empty. One
closure-receipt CI remains required.

## Meaningful partial, falsification, and hard gap

`MEANINGFUL_PARTIAL` requires all of:

- the exact actual phase ratio;
- a proved finite uniform phase-block bound;
- ordered eta convergence with a literal `C*N^(-sigma)` remainder;
- an exact theorem stating that identification with `hardyLittlewoodEta` is the only missing
  edge.

`FALSIFIED_STATEMENT` applies if Lean exhibits a counterexample to the proposed source regime,
ratio formula, denominator bound, or uniform constant. The corrected regime and a compiled
counterexample or contradiction theorem must be recorded.

`HARD_GAP_REDUCED` applies only if the finite phase and eta-remainder chain compiles and the
remaining failure is localized to one exact analytic-identification theorem shape. Tactic
friction is not a hard gap.

## Negative controls

- A bound for arbitrary complex phases is not the actual logarithmic phase theorem.
- Pairing adjacent terms and retaining an `abs(s)` factor does not prove Lemma 3.
- Assuming Hardy--Littlewood Lemma 2 makes the algebraic cancellation conditional and is not
  full success.
- Defining the eta value as an unspecified limit without identifying it with the project's
  zeta expression is only partial success.
- Absolute convergence in `re(s)>1` alone does not close the source half-plane.
- Improving the largest admissible phase constant does not advance the endpoint once one
  fixed positive source-valid constant compiles.
- Lemma 3 is a truncation theorem, not an eta-error mean-square theorem or H1 theorem.

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
