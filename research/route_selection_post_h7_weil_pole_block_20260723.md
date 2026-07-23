# Route Selection after the H7 Weil Pole Block

Date: 2026-07-23

Parent campaign: `LITERATURE-20260723-H7-WEIL-POLE-BLOCK-01`

Parent final-ledger commit: `48e57d28b7e8ec98042cb7f21b836f6eb1c98adc`

Parent public CI: Lean Action run `29971448611`, build job `89094128646`, passed in `1m47s`.

## Governing objective

RH remains the target. Historical-route work seeks source mechanisms that may have been left one
unproved edge from a useful conclusion. A local formalization is selected only when it tests such
a mechanism, not because it increases theorem count or optimizes a numerical constant. Original
conjectures and direct RH attacks remain open at every selection step.

## Cross-route comparison

| candidate | immediate missing object | expected information | present cost/risk | decision |
| --- | --- | --- | --- | --- |
| D6 actual finite prime block | Instantiate the finite von Mangoldt sine source, its atom sum, reflection sectors, and a source-exact sign stress test. | Tests whether the prime term can compensate the newly compiled adverse odd pole sign and whether a termwise semidefinite shortcut survives. | Finite arithmetic and trigonometric algebra; no global limit is needed. | **Selected.** |
| D6 actual archimedean block | Instantiate the digamma-density source and prove positive cutoff increments. | Supplies the third actual block and a monotone tail mechanism. | Requires source-valid digamma positivity, integration, and tail infrastructure not yet aligned in Lean. | High-value successor after the finite prime audit. |
| D6 arithmetic Herglotz scalar bound | Prove the full scalar inequality that would order parity ground states. | Would directly shorten the ranked D6 hard gap. | Premature until the prime and archimedean entries are represented exactly. | Keep open. |
| D3 Bettin--Gonek Mellin/contour bridge | Reconstruct inverse Mellin support, decay, contour shift, and convolution. | Connects the compiled selected-pole coefficient to the arbitrary-length moment obstruction. | High value, but the inversion and contour infrastructure is a larger analytic campaign. | Co-leading cross-route successor. |
| another historical family | Revisit H2/H9/H10/H11/H12/H13/H14 after their first discriminating audits. | Preserves breadth and may expose a new localizer. | Current atlas ranks their surviving edges below D6/D3. | Re-rank after this local endpoint; no family is exhausted. |

## Source mechanism

For an integer cutoff `C >= 2`, the finite-prime source in Groskin,
[arXiv:2607.02828](https://arxiv.org/abs/2607.02828), equation `prime-source`, is

```text
psi_prime(x) = -(1/pi) * sum_{2 <= q <= C}
  (Lambda(q)/sqrt(q)) * sin(2*pi*x*(1-log(q)/log(C))).
```

The von Mangoldt weight vanishes away from prime powers, so the integer interval is the literal
finite prime-power source. The same paper's finite source calculus identifies its
divided-difference matrix with the sum of the single-frequency atom matrices.

The preceding pole audit proves that the pole block is nonnegative on reflection-even vectors and
nonpositive on reflection-odd vectors. Therefore the next useful question is not a better finite
eigenvalue but the actual sign geometry of the prime source. At `C=16,q=8`, the source frequency
is exactly `1/4`. The center-even direction has negative atomic quadratic value while the
edge-odd direction has positive atomic quadratic value. Compiling this would rule out a uniform
semidefinite sign for individual arithmetic atoms in either parity comparison.

## Decision

Select node `H7-WEIL-FINITE-PRIME-SOURCE-INSTANTIATION-01` and preregister campaign
`LITERATURE-20260723-H7-WEIL-PRIME-BLOCK-01`. The endpoint is the source-exact finite atom sum,
reflection-sector preservation, and the exact `C=16,q=8` opposite-sign witness. It does not claim
a sign for the aggregate prime block, the total Weil matrix, or any infinite-cutoff limit.

The preregistration commit `21fad44edcbb9277ca7f3142e776ca2f78d2df09` passed public Lean
Action run `29971859428`, build job `89095368881`, in `1m34s`. The local fixed endpoint then
compiled without a source mismatch. In particular, the `C=16,q=8` atom has the registered
opposite strict parity signs. Frozen implementation commit
`cc264cde977a8b04e596d267aa6656cd8cbf4058` passed run `29973199798`, build job `89099433656`,
in `2m8s`; Lean source is frozen and immutable evidence plus final-ledger gates remain.
