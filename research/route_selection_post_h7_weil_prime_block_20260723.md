# Route Selection after the H7 Finite Weil Prime Block

Date: 2026-07-23

Parent campaign: `LITERATURE-20260723-H7-WEIL-PRIME-BLOCK-01`

Parent final-ledger commit: `26a6f93ccc4b7532f21b50acc2ffbb1debfd338c`

Parent public CI: Lean Action run `29973710220`, build job `89100966535`, passed in `1m33s`.

## Governing objective

RH is the target. Historical-route work tests the actual mechanisms used by human researchers so
that a neglected near-success is not hidden behind a family label or a literature summary. A
family remains active after one campaign. Original conjectures and direct attacks on RH remain
open at every selection step.

## Cross-route comparison

| candidate | immediate missing object | expected information | present dependencies | decision |
| --- | --- | --- | --- | --- |
| H1 Bettin--Gonek `H_t` Mellin identity | Connect the actual real-cutoff Mobius mollifier to `1 / zeta(w - 1/2 + it)` by the source integral. | Closes the first analytic equality in the published off-line-zero obstruction and exposes the exact Fubini boundary. | Existing `farmerMollifier`, an exact logarithmic kernel integral, and the compiled reciprocal-zeta Mobius L-series. | **Selected.** |
| H7 actual archimedean block | Instantiate the digamma-density source, its finite matrices, and cutoff increments. | Completes the third actual source block needed to study prime/pole/archimedean balance. | Digamma real-part estimates, source integration, and tail control still need alignment. | Co-leading successor. |
| H1 inverse Mellin and contour shift | Construct `g_t`, prove support and boundedness, shift the contour, and extract the selected residue. | Would connect the compiled auxiliary coefficient to a power lower bound. | It consumes the `H_t` equality selected here and additional vertical-decay and contour infrastructure. | Follow after this source identity. |
| another historical family | Re-enter H2/H4/H5/H8/H9/H10/H11/H12/H13/H14 at a surviving source mechanism. | Broadens the search for overlooked proof edges. | Ranked after the present H1/H7 source dependencies, not closed or exhausted. | Re-rank after this campaign. |

## Source mechanism

Bettin--Gonek, [arXiv:1604.02740](https://arxiv.org/abs/1604.02740), equation `(2.1)`, defines

```text
M_x(s) log x = sum_{n <= x} mu(n) n^(-s) log(x/n)
```

and, for `Re(w) > 3/2`, states

```text
H_t(w) = integral_1^infinity M_x(1/2+it) log(x) x^(-w) dx
       = 1 / ((w-1)^2 zeta(w-1/2+it)).
```

The project already contains the exact real-cutoff `farmerMollifier`. It also proves

```text
integral_1^infinity log(u)^n u^(-a-1) du = n! / a^(n+1)
```

for `Re(a)>0`, and the Mobius L-series identity `L(mu,q)=1/zeta(q)` for `Re(q)>1`. With
`a=w-1`, scaling `x=n*u` turns each source term into

```text
mu(n) n^(1-w-s) / (w-1)^2.
```

Thus the remaining substantive edge is the source-exact pointwise series representation plus an
absolutely justified sum-integral exchange on `Re(w)>3/2`.

## Decision

Select node `H1-BETTIN-GONEK-H-MELLIN-IDENTITY-01` and preregister campaign
`LITERATURE-20260723-H1-BETTIN-GONEK-MELLIN-IDENTITY-01`. The endpoint is the literal
real-cutoff mollifier identity, its integrability, the scaled logarithmic kernel calculation, the
absolute Mobius-series interchange, and the exact `H_t(w)` reciprocal-zeta formula.

This endpoint does not include inverse Mellin support, vertical decay of `G_t`, contour shifting,
the selected-residue lower bound, a moment-to-power theorem, Farmer's arbitrary-length moment
conjecture, or RH.

## Local outcome

The selected endpoint now compiles from the literal `farmerMollifier`. Lean proves the finite and
pointwise source expansions, the scaled logarithmic kernel, the absolute integrated-norm
majorant on `Re(w)>3/2`, the sum-integral exchange, Mellin convergence, and the exact reciprocal
zeta value. No cutoff, exponent, branch, or boundary mismatch was found.

This moves the H1 mechanism from the displayed identity `(2.1)` to the inverse Mellin,
support/boundedness, decay, convolution, and contour edges. It does not move the RH frontier.
After public closure, the successor must be reranked against the H7 archimedean source block and
other still-underexplored historical mechanisms; the H1 family is not marked exhausted.

Frozen implementation commit `1ca590891a51da76712e8a2dd177287de56d0b43` passed public Lean
Action run `29976558428`, build job `89109449098`, in `2m6s`. The proof source is frozen;
immutable evidence and final-ledger publication remain.
