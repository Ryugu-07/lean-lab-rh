# D9 Conrey--Li Phase Obstruction Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-D9-CONREY-LI-PHASE-OBSTRUCTION-01`

Selected node: `D9-CONREY-LI-PHASE-OBSTRUCTION-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Primary source

J. Brian Conrey and Xian-Jin Li, *A note on some positivity conditions related to zeta- and
L-functions*, 1998, especially Theorem 2, equations `(3.3)`--`(3.4)`, and the concluding Sarnak
remark.

- arXiv: <https://arxiv.org/abs/math/9812166>
- PDF: <https://arxiv.org/pdf/math/9812166>

Theorem 2 derives nonnegative real part of `W(z)/W(z+i)` in the half-plane
`Im(z)>-1/2` from the proposed shifted reproducing-kernel positivity. For
`W(z)=1/xi(1-i*z)`, the paper first gives a numerical negative witness. Its final remark instead
uses density of logarithmic zeta values and a bounded correction to produce a point where the xi
ratio phase lies in a negative-real-part sector.

## Exact fixed endpoint

Create `LeanLab/Riemann/ConreyLiPhaseObstruction.lean` only after public preregistration CI.
Compile:

1. dense complex range implies that the imaginary coordinate is unbounded above and below;
2. a uniformly bounded imaginary correction preserves both forms of unboundedness;
3. a continuous corrected phase on a preconnected nonempty domain takes the exact value `pi`;
4. if `exp(ell(x))=F(x)`, that phase value gives `Re(F(x))<0`;
5. for `z=i*(s-1)` and `W(z)=1/Xi(1-i*z)`, prove exactly
   `W(z)/W(z+i)=(Xi(s)/Xi(s+1))⁻¹` under visible nonvanishing hypotheses;
6. prove that negative real part of the xi ratio gives negative real part of the shifted
   reciprocal ratio;
7. specialize the generic consumer to the actual `riemannXi`, while retaining the source
   density, logarithm, continuity, bounded-correction, strip, and nonvanishing facts as explicit
   premises.

Preferred declaration names:

```lean
conreyLi_im_unbounded_of_denseRange
conreyLi_exists_phase_eq_pi
conreyLi_exists_exp_re_neg
conreyLiShiftCoordinate
conreyLiReciprocalModel
conreyLi_reciprocal_shift_ratio_eq_inv
not_conreyLiShiftRatioNonnegative_of_phase_data
not_conreyLiRiemannXiShiftRatioNonnegative_of_phase_data
```

Names and packaging may change, but every mathematical premise and the actual-xi specialization
must remain visible.

## Proposed aggregate Lean shape

```lean
def ConreyLiShiftRatioNonnegative (W : Complex -> Complex) : Prop :=
  forall z, -(1 / 2) < z.im ->
    0 <= (W z / W (z + Complex.I)).re

theorem not_conreyLiRiemannXiShiftRatioNonnegative_of_phase_data
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    (s ell zetaLog : X -> Complex)
    (hdense : DenseRange zetaLog)
    (hphase : Continuous (fun x => (ell x).im))
    (hbounded : exists C : Real, 0 <= C and
      forall x, |(ell x - zetaLog x).im| <= C)
    (hstrip : forall x, 1 / 2 < (s x).re)
    (hnonzero : forall x, riemannXi (s x) != 0 and
      riemannXi (s x + 1) != 0)
    (hlog : forall x, Complex.exp (ell x) =
      riemannXi (s x) / riemannXi (s x + 1)) :
    not (ConreyLiShiftRatioNonnegative
      (fun z => (riemannXi (1 - Complex.I * z))⁻¹))
```

This theorem is a conditional source-logic endpoint. The project may strengthen it if the actual
value-distribution inputs can be discharged, but may not hide them.

## Hard-gap position

```text
Conrey--Li shifted RKHS positivity
  -> shifted reciprocal ratio has nonnegative real part

known log-zeta value distribution + source branch estimates
  -> dense phase data with bounded correction
  -> shifted reciprocal ratio has negative real part
  -> proposed positivity fails
```

This campaign attacks the second chain after its analytic inputs and the exact ratio-coordinate
translation. It does not formalize the reproducing-kernel Hilbert space or prove Theorem 2 from
first principles.

## Assumption frontier

Available:

- standard topology of dense ranges, connected images, and intermediate values;
- complex exponential, real/imaginary coordinate bounds, inversion, and exact algebra;
- actual project `riemannXi` and its functional identities.

Explicitly unavailable:

- a Mathlib theorem for Bohr--Courant/Voronin density of `log zeta`;
- a source-aligned continuous logarithm branch on the required zero-free strip domain;
- the bounded imaginary correction between `log(xi(s)/xi(s+1))` and `log zeta(s)`;
- a certified `t=282` point-value inequality;
- de Branges/RKHS Theorem 2 as a compiled theorem.

None of these may be replaced by a custom axiom, decimal oracle, or hidden premise.

## Falsification and stopping criteria

- `DENSE_BOUNDED_INSUFFICIENT`: compile a countermodel if dense range plus bounded correction and
  continuous corrected phase on a preconnected domain do not force phase crossing.
- `COORDINATE_MISMATCH`: record the corrected reciprocal or shift identity if the source
  coordinate algebra differs.
- `INVERSION_SIGN_MISMATCH`: compile the exact correction if negative real part is not preserved
  by reciprocal inversion.
- `KNOWN_THEOREM_FRONTIER`: if all source logic compiles but the actual specialization stops at
  value distribution/log-branch inputs absent from Mathlib, classify that boundary honestly and
  stop the fixed campaign.

Local stop returns the active global Goal to `ROUTE_SELECTION`.

## Success criteria

- generic phase crossing and negative-exponential endpoint;
- exact shifted reciprocal coordinate identity;
- actual-xi conditional aggregate theorem with every source input visible;
- proven Target, exact TargetChecks, selected axiom prints, empty forbidden scans,
  warning-as-error production compile, full build, and all public CI gates.

Expected classification:

- `historical_route_coverage_delta=1`;
- `source_logic_bridge_delta=1`;
- `known_theorem_formalization_delta=0` unless the actual value-distribution theorem is compiled;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI.
