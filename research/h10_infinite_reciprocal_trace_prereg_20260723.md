# H10 Infinite Reciprocal-Trace Transfer Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01`

Selected node: `H10-INFINITE-ORDINARY-TRACE-RECIPROCITY-01`

Status: `IMPLEMENTATION_CI_PASSED / EVIDENCE_COMMIT_REQUIRED`

Preregistration commit `8077a2558142a1968b283296e9fc196da02bda93` passed public Lean Action
run `29955908591`, build job `89044796394`, in `2m32s`. Proof-source editing began only after this
gate passed.

Frozen implementation commit `34b307baaca52e043d05668894abe4cceb9a3c2a` passed public Lean
Action run `29956666496`, build job `89047355398`, in `2m25s`. Lean proof source is frozen;
immutable-evidence publication and its own public CI are the next gate.

## Selection reason

D9 final-ledger commit `276282262f033aeb3f106e7eb66180a92b23ec4d` passed public Lean Action
run `29955117117`, build job `89042095525`, in `2m2s`. The generic Suzuki normalization/pole audit
is closed, while the actual canonical-system limit remains open.

Fresh breadth selection compared D3 mollifiers, D4 density, D6 finite-prime spectral work, D7
function-field transfer, and D11 automorphic/Iwasawa stress tests. Another proportion or density
countermodel would repeat the already compiled sparse-exception boundary. Another fixed Galerkin
certificate would return to finite numerical structure. D11 presently lacks a source-backed map
to the individual zeta zero set. D7 has one compiled finite spectral theorem but has not tested the
most literal infinite-spectrum transfer of its ordinary power traces and reciprocal pairing.

The selected audit asks exactly which finite-field input breaks before any new number-field
cohomology is proposed. Original conjectures and direct RH attacks remain open throughout.

## Locked sources

1. Machiel van Frankenhuijsen, "The Riemann Hypothesis for Function Fields over a Finite Field,"
   arXiv:0806.0044, especially equations (3.2)--(3.3) and Lemma 3.1.
   <https://arxiv.org/abs/0806.0044>
2. Pierre Deligne, "La conjecture de Weil I," Publications Mathematiques de l'IHES 43 (1974).
   <https://publications.ias.edu/node/345>
3. Alain Connes, "Trace formula in noncommutative geometry and the zeros of the Riemann zeta
   function," arXiv:math/9811068.
   <https://arxiv.org/abs/math/9811068>
4. Project theorem `norm_eq_sqrt_of_powerSum_bound_and_reciprocal` in
   `LeanLab/Riemann/FinitePowerSumRigidity.lean`.

The function-field source expresses every extension-field point count through a fixed finite
family of Frobenius eigenvalues and ordinary power sums. The project theorem formalizes the final
finite rigidity step. Connes is included only as primary evidence that the number-field explicit
formula is approached through a trace formula requiring a different infinite spectral framework;
none of its open trace claims is used as a premise.

## Exact transfer edge

For a finite spectrum, every power sum is automatically summable and a nonzero reciprocal pairing
is harmless. A direct countably infinite replacement would ask for both:

1. ordinary summability of `alpha(n)^k` for at least one positive integer `k`; and
2. a permutation `sigma` with `alpha(sigma(n))*alpha(n)=q` for a fixed nonzero `q`.

Ordinary summability forces `alpha(n)^k -> 0`. Permutation invariance of summability forces the
paired powers to tend to zero as well. Their products therefore tend to zero, while reciprocal
pairing makes every product equal to `q^k`. For positive `k`, this would force `q=0`.

The conclusion, if compiled, is not that infinite spectral methods fail. It is that a number-field
analogue cannot simultaneously retain the literal nonzero reciprocal pairing and use an ordinary
unregularized power trace of this form. A viable route must change coordinates, truncate with a
uniform tail theorem, or specify a regularized/distributional trace.

## Fixed Lean endpoint

Create `LeanLab/Riemann/InfiniteReciprocalTraceAudit.lean` and compile all of the following without
placeholders or resource relaxation:

1. Define `infiniteSpectrumHasReciprocalPairing alpha sigma q` by the exact pointwise product law.
2. Define ordinary `k`-th power-trace admissibility using
   `Summable (fun n => alpha n ^ k)`; do not use Lean's default value of `tsum` for nonsummable
   families as mathematical evidence.
3. Prove that summability of the `k`-th powers is preserved by the pairing permutation and that
   both the original and paired power sequences tend to zero.
4. For `0 < k`, prove that summability plus reciprocal pairing forces `q=0`.
5. Deduce that a nonzero reciprocal constant prevents ordinary summability of every positive
   power trace.
6. Give an exact nonzero finite reciprocal-pairing witness, showing that the obstruction is caused
   by the countably infinite ordinary-trace transfer rather than by reciprocal pairing itself.
7. Combine the finite witness and infinite obstruction in one aggregate route-audit theorem.

Proposed declarations:

- `infiniteSpectrumHasReciprocalPairing`
- `infiniteSpectrumHasOrdinaryPowerTrace`
- `eq_zero_of_ordinaryPowerTrace_and_reciprocalPairing`
- `not_ordinaryPowerTrace_of_reciprocalPairing`
- `finiteReciprocalPairingWitness`
- `infiniteReciprocalTraceAudit_endpoint`

Names may change to fit Mathlib's summability API, but the positive-power quantifier, nonzero
reciprocal constant, permutation, and ordinary `Summable` conclusion may not be weakened silently.

## Success and falsification criteria

`FULL_SUCCESS` requires the finite/infinite contrast, exact Targets and TargetChecks, selected
standard-only axiom prints, an empty production forbidden scan, full build, and independent public
CI.

`MEANINGFUL_PARTIAL` requires an exact Lean API obstruction after proving the convergence of both
power sequences, without dropping permutation invariance or positivity of the exponent.

`TRANSFER_SURVIVES` requires a no-sorry example with nonzero `q`, a permutation reciprocal pairing,
and ordinary summability of a positive power. Such an example would falsify the proposed
obstruction and reopen the literal transfer.

## Claim boundary

- No curve, Frobenius operator, etale cohomology group, or Riemann-Roch theorem is formalized.
- No zeta zero is represented by `alpha`.
- No statement rules out regularized traces, distributional traces, or source-valid truncations.
- No result is claimed about conditional or order-dependent summation outside Lean's `Summable`.
- The finite spectral rigidity theorem and function-field RH remain untouched.
- The campaign does not prove RH or show that Hilbert-Polya/trace approaches are impossible.

## Mechanical gates

Before proof-source editing:

- publish this preregistration and require public Lean Action CI;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register exact Targets and TargetChecks;
- print selected transitive axioms;
- scan the production module for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and
  `unsafe`;
- run `git diff --check`, the module build, full build, and public CI;
- retain the distinction between finite ordinary traces, infinite ordinary traces, and
  regularized number-field traces.

## Stop and successor rule

Stop this local campaign at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`, `TRANSFER_SURVIVES`, or proof that
the exact endpoint already exists. Local stop returns the persistent RH Goal to the unfinished
historical atlas. H10 remains open unless an actual number-field spectral/trace object and its
uniform infinite tail are constructed. Original conjecture and direct RH attempts remain open.
