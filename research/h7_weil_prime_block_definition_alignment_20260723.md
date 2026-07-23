# H7 Finite Weil Prime Block Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H7-WEIL-PRIME-BLOCK-01`

Production module: `LeanLab/Riemann/WeilGroundStatePrimeBlock.lean`

## Source object

The source is Groskin, [arXiv:2607.02828](https://arxiv.org/abs/2607.02828), equation
`prime-source` and the finite source-calculus lemma. The paper writes

```text
psi_prime(x) = -(1/pi) * sum_{q=p^a <= c}
  Lambda(q)/sqrt(q) * sin(2*pi*x*(1-log(q)/log(c))).
```

The Lean endpoint restricts the cutoff to an integer `C >= 2` and sums over `Finset.Icc 2 C`.
This is not an arithmetic relaxation: Mathlib's von Mangoldt function is zero exactly away from
prime powers. Lean explicitly proves that the atom coefficient vanishes when `q` is not a prime
power and is strictly negative for prime powers `q >= 2`.

## Coordinate table

| source coordinate | Lean definition | exact alignment |
| --- | --- | --- |
| `1-log(q)/log(C)` | `weilPrimeFrequency C q` | lies in `[0,1]` for `2 <= q <= C` |
| `-Lambda(q)/sqrt(q)` | `weilPrimeAtomCoefficient q` | nonpositive; zero off prime powers; strictly negative on prime powers |
| sine atom | `weilPrimeAtomSource C q` | literal source function |
| value sample | `weilPrimeAtomSourceValue C q N i` | source at centered integer frequency |
| derivative sample | `weilPrimeAtomSourceDerivative C q N i` | certified by `hasDerivAt_weilPrimeAtomSource_centered` |
| aggregate source | `weilPrimeSourceValue`, `weilPrimeSourceDerivative` | finite sum over `2 <= q <= C` |
| atom matrix | `weilFinitePrimeAtomMatrix C q N` | divided difference with the certified diagonal derivative |
| aggregate matrix | `weilFinitePrimeSourceMatrix C N` | divided difference of the aggregate samples |

The matrix identity is proved from the source samples:

```text
Q_prime(C,N) = sum_{2 <= q <= C} Q_atom(C,q,N).
```

It is not used as the definition of `Q_prime`.

## Reflection alignment

Each sine value sample is reflection-odd and each cosine derivative sample is reflection-even.
Therefore the aggregate divided-difference matrix satisfies

```text
Q_prime(i.rev,j.rev) = Q_prime(i,j)
```

and preserves both reflection-even and reflection-odd finite sectors. This establishes the exact
parity interface needed by the existing finite Herglotz and simple-even certificates, but it does
not establish either required strict inequality.

## Exact sign witness

For `C=16` and the actual prime power `q=8`, Lean proves

```text
omega(16,8) = 1/4,
a(8) < 0.
```

At level `N=1`, let

```text
e = [0,1,0],
o = [1,0,-1].
```

Lean proves that `e` is reflection-even, `o` is reflection-odd, and

```text
e dot (Q_atom(16,8,1) * e) = a(8)/2 < 0,
o dot (Q_atom(16,8,1) * o) = -2*a(8)/pi > 0.
```

Thus one genuine arithmetic source atom has opposite strict signs on the two parity sectors. A
proof that assigns every individual prime atom one common semidefinite sign cannot establish the
total parity ordering.

## Claim boundary

The witness is not a sign theorem or counterexample for the aggregate prime block through `16`.
Other prime-power atoms can cancel it. The module does not define the archimedean block, assemble
the total Weil matrix, prove the arithmetic Herglotz scalar inequality, prove simple-even
uniformity, compare a ground state with the prolate vector, pass either cutoff to a limit, prove
H7, or prove RH.

The useful delta is exact mechanism information: the pole block has an adverse odd sign, while a
prime constituent is already parity-indefinite in the compensating direction. Any successful
proof must use aggregate arithmetic and archimedean balance rather than termwise positivity.

## Mechanical status

- Production module: 297 lines, standalone diagnostic-free compile.
- Module build: 8,650 jobs passed.
- Targets: one new proven actual finite-prime-source Target; the source ratio Target remains open.
- Exact TargetChecks: 12 new witnesses compile.
- Axiom audit: 9 selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Production forbidden scan: empty.
- Direct compiles: production module, Targets, TargetChecks, and AxiomsAudit pass.
- Full build: 8,754 jobs passed.
- Frozen implementation: commit `cc264cde977a8b04e596d267aa6656cd8cbf4058` passed public Lean
  Action run `29973199798`, build job `89099433656`, in `2m8s`.
- Immutable evidence: commit `6a697d92caa485fe1f274ffb5495e8cd3379b297` passed public Lean
  Action run `29973451920`, build job `89100185836`, in `2m20s`.
- `rh_frontier_delta=0`; `hard_gap_delta=0`; `actual_source_block_delta=1`;
  `obstruction_map_delta=1`.
