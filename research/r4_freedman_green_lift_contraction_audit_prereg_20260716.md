# R4 Freedman Green-Lift Contraction Audit Preregistration

Audit: `AUDIT-20260716-R4-FREEDMAN-GREEN-LIFT-CONTRACTION-01`

Date: 2026-07-16

Status: `LOCAL_VERIFICATION_COMPLETE`

## Source Claim Under Audit

Freedman's 2026 preprint constructs a normalized Weyl/Volterra quotient model and, in the
section titled *Trace Schur Kernel as a Volterra--Green Feature Form*, writes the compressed
factorization

```text
G_- = C K E G_+,
```

where the multiplier `K` is pointwise contractive. It also records trace-fiber Euler--Lagrange
orthogonality `Q(f_x,h)=0` for `h` in the trace kernel, and then declares the completed compressed
map `C K E` contractive. The e-print package contains the TeX source only; the many Python scripts
referenced as certificates are not included.

Primary source:

- Marvin B. Freedman, *Finite-core Volterra reductions for a Weyl-positive Riemann phase
  kernel*, arXiv:2606.29555: https://arxiv.org/abs/2606.29555

Closest operator-theoretic reference:

- R. G. Douglas, *On majorization, factorization, and range inclusion of operators on Hilbert
  space*, Proc. AMS 17 (1966), 413--415:
  https://www.ams.org/journals/proc/1966-017-02/S0002-9939-1966-0203464-1/

Douglas-type factorization requires a genuine operator majorization/range hypothesis. A
contractive middle multiplier does not by itself control the norm of the surrounding compression
and right-inverse maps.

## Candidate Screen

1. **Theta-mode differential identity.** It survives symbolic differentiation but is an exact
   source identity, not the claimed positivity bridge; reject it as the audit endpoint.
2. **Finite-dimensional injective trace gives some positive frame floor.** This is qualitatively
   true by compactness. It does not certify the manuscript's displayed numerical constant, but
   the surrounding numerical hypotheses are under-specified; reject it as the exact endpoint.
3. **Positive branch weights give uniform `omega` contraction.** Positive weights do not
   automatically preserve an operator comparison, but the source does not provide enough fixed
   Hilbert norms for a faithful finite countermodel; defer.
4. **KLM positivity implies the intended de Branges/RH endpoint.** The manuscript explicitly
   leaves the transmutation/pullback open; it is not a completed claim to falsify.
5. **Green-lift listed premises force `C K E` contraction.** This has a faithful finite-dimensional
   abstraction and fails in a two-dimensional model with a nontrivial trace kernel. Select it.

## Fixed Countermodel

Use the real space `V=Real x Real`, trace `R(x,y)=x`, and Green representative `f_x=(x,0)`.
Define

```text
G_+(x,y)=x,       G_-(x,y)=2x,
K(t)=t/2,         E(t)=t,          C(t)=4t,
Q(v,w)=G_+(v)G_+(w)-G_-(v)G_-(w).
```

Then:

- `R(f_x)=x` and `ker R` is nontrivial;
- `Q(f_x,h)=0` for every `h` with `R(h)=0`;
- `|K(t)|<=|t|` for every `t`;
- `G_-(f_x)=C(K(E(G_+(f_x))))`;
- nevertheless `C K E` multiplies by two, and `Q(f_1,f_1)=-3`.

The proposed bundled Lean endpoint is

```lean
theorem freedmanGreenLift_listedPremises_do_not_force_contraction :
    (forall x, freedmanTrace (freedmanGreenRepresentative x) = x) and
    (forall x h, freedmanTrace h = 0 ->
      freedmanGreenForm (freedmanGreenRepresentative x) h = 0) and
    (forall t, abs (freedmanMultiplier t) <= abs t) and
    (forall x, freedmanNegativeFeature (freedmanGreenRepresentative x) =
      freedmanCompression
        (freedmanMultiplier
          (freedmanLift (freedmanPositiveFeature (freedmanGreenRepresentative x))))) and
    not (forall x,
      abs (freedmanCompression
        (freedmanMultiplier
          (freedmanLift (freedmanPositiveFeature (freedmanGreenRepresentative x))))) <=
        abs (freedmanPositiveFeature (freedmanGreenRepresentative x))) and
    freedmanGreenForm (freedmanGreenRepresentative 1)
      (freedmanGreenRepresentative 1) < 0
```

ASCII logical connectives are used above for portability in the preregistration; the Lean module
may use the corresponding Unicode notation. Harmless naming and reassociation changes are
allowed. The endpoint must retain the nontrivial trace-kernel witness and the exact negative
quadratic value.

## Repaired Abstract Condition

The same Lean batch should prove the elementary repair: if `C`, `K`, and `E` are each contractions
in the relevant norms, then `C o K o E` is a contraction. This does not establish those hypotheses
for the source's concrete Volterra operators; it records the missing dependency precisely.

## DAG And Scope

- `work_class`: `LITERATURE` with a Lean falsification endpoint
- `route`: R4 spectral/Weyl/Volterra positivity
- `hard_gap_before`: G6/W1 and G7/W2 open; G3/M2 parked
- `hard_gap_after_if_complete`: unchanged
- `hard_gap_delta`: 0
- `assumption_frontier_before`: the source treats multiplier contraction plus trace-fiber
  orthogonality as sufficient for the compressed Green lift to be contractive
- `assumption_frontier_after_if_complete`: a separate norm estimate for the compression/right
  inverse, or an exact energy identity proving their combined contraction, is required
- `classification_if_complete`: `BRANCH_ELIMINATED`

This audit does not claim the concrete Weyl kernel is nonpositive and does not infer RH or its
negation. It rejects only the displayed sufficiency argument from the listed premises.

## Rejection Conditions

- Do not substitute a numerical matrix experiment for the exact scalar calculation.
- Do not claim that the full Volterra route or KLM positivity is false.
- Do not infer anything about RH.
- Reject any `sorry`, `admit`, `native_decide`, project axiom, unsafe declaration, or resource-limit
  relaxation.

## Lean Result

The preregistered model is proved in `LeanLab/Riemann/FreedmanGreenLiftAudit.lean`. The bundled
endpoint is `freedmanGreenLift_listedPremises_do_not_force_contraction`. In particular, Lean
checks a genuinely nonzero vector in `ker R`, the complete factorization and orthogonality
premises, failure of the compressed contraction at `x=1`, and the exact signed value `-3`.

The same module proves `contraction_comp_three`, recording a sufficient repaired condition. This
does not supply the missing contraction hypotheses for the source's concrete `C` and `E`.

## Local Verification

- Standalone compilation and the 2,966-job dedicated module build pass without warnings.
- Exact Targets and TargetChecks, including the full bundled statement, compile.
- Both selected transitive axiom prints contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-token, declaration, resource-relaxation, and scratch-name scans are empty.
- `git diff --check` and the full 8,676-job build pass.

The local classification is `BRANCH_ELIMINATED` for the displayed listed-premise inference, with
`hard_gap_delta=0`. The broader Weyl/Volterra program and the persistent RH Goal remain active.
