# H7 Finite Weil Prime Block Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H7-WEIL-PRIME-BLOCK-01`

Selected node: `H7-WEIL-FINITE-PRIME-SOURCE-INSTANTIATION-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `48e57d28b7e8ec98042cb7f21b836f6eb1c98adc`.
- `parent_public_ci`: Lean Action run `29971448611`, build job `89094128646`, passed in `1m47s`.
- `global_goal`: active; RH remains open.
- `route_selection`: `research/route_selection_post_h7_weil_pole_block_20260723.md`.
- `production_gate`: no production Lean source may be created before this preregistration commit
  passes public Lean Action CI.

## Primary source alignment

The fixed source is Groskin, [arXiv:2607.02828](https://arxiv.org/abs/2607.02828), equations
`prime-source` and the finite source-calculus lemma. For integer cutoff `C >= 2`, use

```text
omega(C,q) = 1 - log(q)/log(C),
a(q) = -Lambda(q)/sqrt(q),
psi_q(x) = a(q)/pi * sin(2*pi*omega(C,q)*x),
psi_prime(x) = sum_{q in Icc 2 C} psi_q(x).
```

This is equal to the paper's prime-power sum because `Lambda(q)=0` when `q` is not a prime power.
Diagonal samples must be the literal derivative

```text
psi_q'(x) = 2*a(q)*omega(C,q)*cos(2*pi*omega(C,q)*x).
```

No closed entry may be postulated independently of these value and derivative samples.

## Fixed Lean endpoint

1. Define `weilPrimeFrequency`, `weilPrimeAtomCoefficient`, atom value/derivative samples, their
   finite aggregate, and the corresponding divided-difference matrices.
2. Prove `0 <= omega(C,q) <= 1` whenever `2 <= q <= C` and `2 <= C`.
3. Prove `a(q) <= 0`, with strict negativity for prime powers `q >= 2`.
4. Prove every atom value sample is reflection-odd and every atom derivative sample is
   reflection-even.
5. Prove the aggregate source samples have the same parity.
6. Prove the aggregate source matrix equals the finite sum of the atom matrices entrywise.
7. Prove aggregate matrix reflection symmetry and preservation of both finite even and odd
   sectors.
8. Prove `omega(16,8)=1/4` and certify that `q=8` is an actual nonzero von Mangoldt atom.
9. Define explicit level-one center-even and edge-odd witness vectors, prove their parity, and
   prove the `C=16,q=8` atom has a strictly negative quadratic value on the even witness and a
   strictly positive value on the odd witness.
10. Package the source decomposition, sector preservation, and opposite-sign atom witness in one
    aggregate endpoint theorem.

## Decision criteria

- `FULL_SUCCESS_AT_PRIME_ENDPOINT`: all ten items compile with no `sorry`; exact TargetChecks and
  selected axiom prints pass; the full build and all public evidence gates pass.
- `PARTIAL_SOURCE_ALIGNMENT`: the source and reflection statements compile but the exact sign
  witness or atom-sum identity exposes a normalization issue. Record the precise failed equality.
- `SOURCE_MISMATCH`: the paper's integer-cutoff formula does not match the literal von Mangoldt
  source, derivative diagonal, or centered-frequency convention. Stop and register the mismatch.
- `FALSIFICATION_VALUE`: the opposite-sign witness proves that individual prime atoms cannot be
  assigned one semidefinite sign across both parity sectors.

## Claim boundary

The `C=16,q=8` witness concerns one genuine constituent of the finite prime source, not the full
sum through `16`. The campaign proves no sign for the aggregate prime block, no sign for the sum
of prime, pole, and archimedean blocks, no arithmetic Herglotz scalar inequality, no simple-even
ground-state theorem, no cutoff-uniform convergence, no H7, and no RH.

The archimedean source, the Guinand--Weil infinite zero sum, and every source-limit theorem are
unavailable as premises. Numerical eigenvalue experiments may guide debugging but cannot satisfy
any endpoint.

## Mechanical gates

Production code must pass direct compilation, exact TargetChecks, selected `#print axioms`, an
empty forbidden-token scan, `git diff --check`, and the full `lake build`. Publication requires a
frozen implementation CI, immutable-evidence CI, and final-ledger CI. The proof source is frozen
after implementation CI.

## Preregistration public gate

- `commit`: `21fad44edcbb9277ca7f3142e776ca2f78d2df09`.
- `public_ci`: Lean Action run `29971859428`, build job `89095368881`, passed in `1m34s`.
- `effect`: the fixed production proof-source gate is open.

## Local endpoint result

The 297-line production module compiles all fixed source, derivative, atom-sum, reflection, and
sign-witness items. Lean proves the integer-cutoff von Mangoldt source is literal, including
vanishing off prime powers and certified diagonal derivatives. The `C=16,q=8` atom has exact
negative even and positive odd quadratic directions. One proven Target, 12 exact TargetChecks,
9 selected standard-only axiom prints, an empty production forbidden scan, `git diff --check`,
and the 8,754-job full build pass. This is `FULL_SUCCESS_AT_PRIME_ENDPOINT` locally, pending public
implementation and evidence gates. Frozen implementation commit
`cc264cde977a8b04e596d267aa6656cd8cbf4058` passed public Lean Action run `29973199798`, build
job `89099433656`, in `2m8s`; Lean source is frozen and immutable evidence plus final-ledger gates
remain. Immutable-evidence commit `6a697d92caa485fe1f274ffb5495e8cd3379b297` passed run
`29973451920`, build job `89100185836`, in `2m20s`. Only final-ledger CI remains. Every excluded
aggregate and limit edge remains open.
