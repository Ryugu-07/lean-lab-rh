# Route Selection after H12 Boundary-Sign Closure

Date: 2026-07-26

Parent final ledger: `53f781929605243e05dcec36bb188afb1b0c50a5`

Parent public CI: Lean Action run `30193513376`, build job `89770844367`, passed in `1m51s`.

## Fresh comparison

| candidate | compiled frontier | exact missing object | decision |
| --- | --- | --- | --- |
| H12 Levinson--Montgomery critical-zero indentation | Closed equation `(2.1)`, both vertical signs, local xi factorization with multiplicity, residual-log-derivative continuity, and the strict principal-pole sign compile. | Prove strict negativity on a complete small left indentation around every critical-line zero above height `10`, including the two critical-line endpoints. | **Selected.** This is the next literal paragraph of the primary proof, and the frozen local factor exposes a stronger punctured-half-neighborhood attack not available before the parent campaign. |
| H1 arbitrary-length mollified moments | The full Bettin--Gonek conditional bridge from Farmer's moment bound to RH compiles. | Prove the open uniform mollified second-moment estimate for arbitrary positive length exponent. | Direct RH-strength reserve; no unformalized known bridge remains between the compiled endpoint and the open estimate. |
| H2/H11 exceptional-zero amplification | The half-isolated geometry, horizontal-multiplicity consumer, and sparse countermodels compile. | Find an arithmetic theorem forcing one actual off-line orbit to produce a non-sparse detector defect. | Discovery reserve; no source-backed amplifier was found in the current comparison. |
| H7/H10 spectral or function-field transfer | The finite Weil dictionary and explicit formula, generic real-zero mechanism, finite Frobenius rigidity, and ordinary infinite-trace obstruction compile. | Construct the actual number-field spectral/cohomological object, positivity, and a uniform regularized tail. | Structural reserve; the missing object is not supplied by another unformalized source theorem. |
| D9 Conrey--Li de Branges obstruction | The atlas records the failed positivity condition, but no actual-zeta witness is kernel-checked. | Certify either the source's high-height negative xi ratio or Sarnak's universality-based existence proof, then connect it to the reproducing-kernel condition. | Important historical boundary, but it first needs high-point-value certification or a universality library. Retain as the leading breadth candidate after the fixed H12 edge. |

H6 direct attacks on `Lambda<=0` remain open, while numerical upper-bound optimization stays
parked under the user's 2026-07-22 ruling.

## Primary-source reconstruction

Levinson and Montgomery, *Zeros of the derivatives of the Riemann zeta-function*, Acta
Mathematica 133 (1974), page 52, argue that at a critical-line zero `rho` the single term
`1/(s-rho)` becomes arbitrarily large on a small left semicircle, so the paired sum is positive
and `Re(zeta'/zeta)<0` on an appropriately indented critical boundary.

The source sentence suppresses a uniformity detail: the real part of the principal pole tends to
zero at the two semicircle endpoints. The parent campaign proved strict negativity at all
zero-free critical-boundary points, but a formal proof must glue those endpoint signs to the
middle-arc pole dominance.

## New attack angle

The local xi factorization gives

```text
xi(z) = (z-rho)^m g(z)
```

with `g(rho)!=0`. On the punctured neighborhood,

```text
zeta'/zeta = m/(z-rho) + R(z),
```

where `R` is continuous. The functional equation forces the xi residual logarithmic derivative
to have zero real part at a critical-line zero. After subtracting the pole/Gamma factor, the real
part of `R(rho)` is exactly the already compiled strictly negative archimedean term.

If this identity compiles, continuity makes `Re R(z)<0` throughout a small disk. The principal
term has nonpositive real part on the closed left half-plane, so the whole punctured left
half-disk is strictly negative. This is stronger than endpoint/middle-arc gluing and immediately
supplies every sufficiently small left semicircle.

## Claim boundary

The campaign does not prove:

- the certified bottom sign on `t=10`;
- a cofinal admissible top-height sequence;
- the argument-principle change in argument on the indented rectangle;
- the exact zeta/zeta-derivative count equality;
- the Jensen `O(log T)` count difference;
- the full Levinson--Montgomery theorem, Speiser equivalence, or RH.

The global RH Goal remains active. Closing or obstructing this fixed edge returns the next loop
to fresh historical route selection.
