# H12 Levinson--Montgomery Critical-Zero Indentation Preregistration

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-CRITICAL-INDENTATION-01`

Selected node: `H12-LM-CRITICAL-INDENTATION-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `FULL_CRITICAL_INDENTATION_SUCCESS_LOCAL / IMPLEMENTATION_CI_REQUIRED`

## Primary source

Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the Riemann zeta-function*,
Acta Mathematica 133 (1974), 49--65, Theorem 1 and the critical-line indentation paragraph on
source page 52.

- DOI: <https://doi.org/10.1007/BF02392141>
- Full text:
  <https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf>

The source states that for a zero `rho0=1/2+i*gamma0`, one can make the single reciprocal term
arbitrarily large by taking `|s-rho0|` small, and concludes that
`Re(zeta'/zeta)<0` on a small left semicircle. At the two endpoints the principal real part is
zero, so this campaign makes the missing uniform endpoint logic explicit.

## Parent state

- `parent_campaign`:
  `LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-BOUNDARY-SIGNS-01`.
- `parent_final_ledger`: commit `53f781929605243e05dcec36bb188afb1b0c50a5`
  passed public run `30193513376`, build job `89770844367`, in `1m51s`.
- `compiled_inputs`: generic non-pole GammaR calculus, closed equation `(2.1)`, strict
  left-boundary and zero-free critical-boundary negativity, local analytic xi factorization with
  multiplicity, residual-log-derivative continuity, and strict left-pointing principal-pole sign.
- `new_material_difference`: prove the real sign of the normalized residual at the zero itself
  and use continuity to obtain a complete punctured left half-neighborhood, rather than proving
  another isolated principal-term inequality.

## Mandatory Lean endpoints

The intended module is
`LeanLab/Riemann/LevinsonMontgomeryCriticalIndentation.lean`.

Names may be adjusted for Lean conventions. The main statement may expose an equivalent
metric-ball or filter formulation, but it must retain actual zeta, actual xi multiplicity, strict
negativity, nonvanishing, the closed left side, and a positive radius.

```lean
theorem levinsonMontgomery_zeroFactor_logDeriv_re_eq_zero
    {rho : Complex} {m : Nat} {g : Complex -> Complex}
    (hrho : IsNontrivialZero rho) (hrhoRe : rho.re = 1 / 2)
    (hm : 0 < m) (hg : AnalyticAt Complex g rho) (hgne : g rho != 0)
    (hfactor : riemannXi =ᶠ[nhds rho]
      fun z => (z - rho) ^ m * g z) :
    (logDeriv g rho).re = 0

theorem exists_levinsonMontgomery_critical_zero_left_neighborhood
    {rho : Complex} (hrho : IsNontrivialZero rho)
    (hrhoRe : rho.re = 1 / 2) (hrhoIm : 10 < rho.im) :
    exists epsilon : Real, 0 < epsilon and
      forall z : Complex, dist z rho < epsilon -> z != rho ->
        z.re <= 1 / 2 ->
        riemannZeta z != 0 and (logDeriv riemannZeta z).re < 0

theorem exists_levinsonMontgomery_negative_left_semicircle
    {rho : Complex} (hrho : IsNontrivialZero rho)
    (hrhoRe : rho.re = 1 / 2) (hrhoIm : 10 < rho.im) :
    exists r : Real, 0 < r and
      forall z : Complex, dist z rho = r -> z.re <= 1 / 2 ->
        riemannZeta z != 0 and (logDeriv riemannZeta z).re < 0
```

The first theorem is the preferred normalization lemma. If the local analytic factor returned by
Mathlib requires an equivalent residual definition, the exact statement may quantify that
residual explicitly, but it may not assume its real part vanishes or is negative.

## Position in the hard-gap DAG

```text
critical-line xi zero + local analytic multiplicity factor
  -> punctured xi logarithmic derivative = principal pole + analytic residual
functional equation + zero-free critical-line approach
  -> residual xi logarithmic derivative has real part zero at the center
closed xi/Gamma/zeta logarithmic derivative identity
  -> zeta residual real part = strictly negative archimedean term
continuity + principal real part <=0 on the closed left side
  -> punctured left half-neighborhood negativity
  -> complete source indentation semicircle negativity
```

This campaign attacks every displayed arrow. It does not construct the complete indented
rectangle or count its zeros.

## Assumption frontier

Available unconditional inputs:

- the actual analytic xi function and actual zeta;
- strict critical-strip bounds for every nontrivial xi zero;
- xi functional-equation and conjugation symmetries;
- local analytic order factorization of xi with positive multiplicity and nonzero analytic unit;
- continuity of the unit's logarithmic derivative;
- generic non-pole GammaR differentiation and the exact xi/Gamma/zeta logarithmic derivative;
- strict negativity of the archimedean term for
  `0<=Re(s)<=1/2`, `Im(s)>=10`;
- strict negativity of `Re(zeta'/zeta)` at every zero-free critical-boundary point above `10`.

Unavailable and prohibited as hidden premises:

- a zero table, simplicity of zeta zeros, RH, or Speiser's conclusion;
- the desired residual sign or semicircle sign;
- uniform separation between distinct critical-line zeros;
- compact contour admissibility, argument principle, or any zero-count equality;
- a custom axiom or numerical point-value oracle.

## Registered attacks

### Attack A: punctured analytic-factor logarithmic derivative

Shrink the factorization neighborhood until `g` is nonzero. On its punctured part, differentiate
`xi(z)=(z-rho)^m*g(z)` and prove

```text
logDeriv xi(z) = m/(z-rho) + logDeriv g(z).
```

No totalized division value at `z=rho` may be used as a limit.

### Attack B: critical-line residual at the center

Approach `rho` through zero-free critical-line points inside the factorization neighborhood.
There the paired-sum identity gives `Re(logDeriv xi)=0`, while the principal pole is purely
imaginary. Pass to the center using continuity of `logDeriv g`.

Fallback B is to differentiate the local factor symmetry induced by
`xi(1-conj(z))=conj(xi(z))`. Either route must prove, not assume, the residual identity.

### Attack C: strict residual neighborhood and source semicircle

Rearrange the exact xi/Gamma/zeta logarithmic derivative on the punctured neighborhood. At the
center, identify the zeta residual real part with the compiled archimedean term and prove it is
strictly negative. Continuity supplies a disk where the residual stays negative. Add the
nonpositive principal real part on `Re(z)<=1/2`, prove zeta nonvanishing away from the center,
and derive both mandatory neighborhood and semicircle endpoints.

Fallback C is an explicit endpoint-neighborhood plus compact middle-arc gluing proof. It counts
as success only if the entire closed left semicircle, including both endpoints, is covered.

## Success criteria

`FULL_CRITICAL_INDENTATION_SUCCESS` requires:

- both mandatory geometric endpoints;
- actual zeta/xi and analytic multiplicity, with no simplicity assumption;
- a proven Target and exact TargetChecks;
- selected transitive axiom prints;
- empty forbidden scans;
- direct warning-as-error module compilation and full `lake build`;
- frozen implementation, immutable-evidence, and final-ledger public CI.

If only the complete source semicircle compiles and the stronger punctured-half-neighborhood is
formally false, classify the exact result separately and retain a counterexample to the stronger
statement.

## Falsification and stopping criteria

- `XI_RESIDUAL_REAL_MISMATCH`: the analytic unit's logarithmic derivative need not have zero real
  part at the center under the actual xi symmetries. Compile the corrected invariant or an exact
  counterexample and stop the half-neighborhood claim.
- `ARCHIMEDEAN_RESIDUAL_MISMATCH`: the normalized zeta residual differs from the source
  archimedean term. Compile the exact correction and reassess its sign.
- `TOTALIZED_LOGDERIV_LEAK`: any argument uses `logDeriv f rho=0` at a zero as limit evidence.
  Replace it with a punctured identity before proceeding.
- `ENDPOINT_GLUE_FAILURE`: middle-arc dominance does not extend to both critical-line endpoints.
  Record the exact missing continuity or isolation theorem; do not claim a complete indentation.
- `local_stop`: full public closure or the first exact obstruction after Attacks A--C. A local
  stop returns to `ROUTE_SELECTION`; the global RH Goal remains active.

## Claim boundary

Success does not prove the bottom `t=10` certificate, a cofinal admissible top sequence, the
argument-principle count, the `O(log T)` comparison, the full Levinson--Montgomery theorem,
Speiser equivalence, or RH.

Expected classification on full success:

- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `known_theorem_formalization_delta=0` until the full Levinson--Montgomery theorem;
- `hard_gap_delta=0` for RH;
- `rh_frontier_delta=0`.

## Production gate

No production Lean proof source may be created or edited until this docs-only preregistration
passes public Lean Action CI.

The gate passed at preregistration commit
`54b5eabdf46acf44878db80cf2e38657f7fb7378`, public Lean Action run `30193955050`,
build job `89772029846`, in `1m35s`.

## Local result

The complete fixed endpoint compiles in the 468-line
`LeanLab/Riemann/LevinsonMontgomeryCriticalIndentation.lean` module.

Attack B used the registered symmetry fallback rather than a limiting sequence of zero-free
critical-line points. The exact local factor and
`riemannXi (1-conj(z))=conj(riemannXi z)` imply a reflected identity for the analytic unit.
Differentiating that identity at the center proves
`Re(logDeriv g rho)=0` without evaluating the totalized logarithmic derivative of xi at its
zero.

Dividing the xi factor by the nonvanishing analytic xi/zeta unit produces the actual zeta
factor. Its residual logarithmic derivative at the center has real part equal to the compiled
archimedean term and is therefore strictly negative for `rho.im>=10`. Analyticity makes that
residual negative and nonvanishing in a neighborhood. At every distinct point on the closed
left side, the exact multiplicity term `m/(z-rho)` has nonpositive real part. Adding the two
terms proves the stronger punctured-left-half-neighborhood endpoint and hence a complete
positive-radius left semicircle including both critical-line endpoints.

## Local mechanical audit

- direct production compile with `-DwarningAsError=true`: pass with no diagnostics;
- proven Target and six exact TargetChecks: pass;
- five selected transitive axiom prints: only `propext`, `Classical.choice`, `Quot.sound`;
- placeholder, custom-declaration, and resource-relaxation scans: empty;
- `git diff --check`: pass;
- full build: `8767/8767`.

Local classification:

- `result=FULL_CRITICAL_INDENTATION_SUCCESS`;
- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `known_theorem_formalization_delta=0` until the full count theorem;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

The implementation is not yet public-green. The bottom `t=10` certificate, cofinal admissible
top contours, the global indented argument principle, exact zeta/zeta-derivative count equality,
the `O(log T)` comparison, the full Levinson--Montgomery theorem, Speiser equivalence, and RH
remain open.
