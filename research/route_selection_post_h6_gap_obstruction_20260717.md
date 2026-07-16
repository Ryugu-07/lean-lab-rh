# Route Selection after the H6 Adjacent-Gap Obstruction

Date: 2026-07-17

Decision: `SELECT H6 heat-Li moment structure / DISCOVERY-20260717-H6-HEAT-LI-MOMENTS-01`

## Comparison

| target | mathematical value | checked leverage | current obstacle | decision |
| --- | --- | --- | --- | --- |
| Repeat generic H6 zero repulsion | direct H6-E if successful | complete local force and trajectory interface | `OBS-H6-ADJACENT-GAP-EIGHT-01` proves the generic bound sharp | reject without a theta-specific input |
| H6-Q certified `Lambda <= 1/5` | unconditional quantitative improvement | source heat family and strip machinery | strictly weaker than RH and requires a large interval-arithmetic stack | defer |
| Direct W2/G7 positivity | RH-equivalent | complete Gaussian and compact explicit-formula criteria | no new global arithmetic cancellation survived the prime-kernel obstruction | eligible, no new attack selected |
| Direct M2/G3 approximation | RH-equivalent | complete Baez-Duarte criterion and Burnol obstruction theory | no explicit new approximant family beyond the recorded failed projection, ladder, and sparse-Gram mechanisms | eligible, no new attack selected |
| H6 heat-Li positive-moment structure | finite Li spine below H6-X; possible scalable theta-specific mechanism | source `Phi>0`, all-time heat integrability, two spatial derivatives, log-derivative algebra, and the generic reverse-Li countermodel | must prove an actual weighted Cauchy-Schwarz inequality and exact derivative normalization | select |

## Material difference from the failed branch

The closed adjacent-gap branch used only real-zero geometry and the heat PDE. The new attack uses
the source representation itself: after the coordinate `z=-i*(2*s-1)`, values and derivatives at
`s=1` are positive weighted `cosh`/`sinh` moments of the exact theta kernel. The polynomial model
in `H6ReverseHeatLiAudit.lean` is not such a positive transform and therefore does not satisfy the
new premise.

The selected finite endpoint is not RH progress. Its value is diagnostic: it identifies a
kernel-specific positivity mechanism that survives the two generic H6 obstruction audits and
tests whether a moment hierarchy can scale toward the all-index Li criterion. Failure at the
second coefficient records a precise obstruction; success licenses only the compiled finite
statements, not an all-index conjecture.

## Source search

- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function,
  and a new upper bound for the de Bruijn-Newman constant*, supplies the exact source heat family.
- The Li/Bombieri-Lagarias criterion supplies the all-index zero-location context.
- A bounded primary-source search found heat-deformation literature but no source establishing
  this exact all-real-time first-two moment statement. No novelty or priority claim is made.

## Next state

Preregister the exact source definitions, moment identities, positivity endpoint, Cauchy-Schwarz
witness, countermodel boundary, and stop conditions. Proof-source edits begin only after the
preregistration commit passes public Lean Action CI.
