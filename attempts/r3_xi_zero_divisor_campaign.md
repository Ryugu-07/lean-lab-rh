# R3 Xi Zero-Divisor Campaign

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-XI-DIVISOR-01`

Route: R3, Li and Weil positivity

Result: `BRIDGE_REDUCED`

`hard_gap_delta=1` for the explicitly inventoried divisor/local-multiplicity prerequisite.

RH assumption frontier: unchanged.

Novelty: `KNOWN_STRUCTURE_PROJECT_ALIGNMENT`.

## Fixed Target

The preregistered batch asked for one global, locally finite divisor of the project-local
`riemannXi`, with finite natural multiplicities, exact support `IsNontrivialZero`, compact-local
finiteness, and multiplicity symmetry under `s |-> 1-s`. A partial generic divisor wrapper did not
count.

## Adversarial Results

1. **Negative even zeta zeros.** These are not xi zeros. Lean reflects every
   `s = -2*(n+1)` to `1-s`, whose real part is greater than one, and uses unconditional zeta
   nonvanishing there. This proves `riemannXi_ne_zero_of_isTrivialZeroPoint`.
2. **The points zero and one.** Existing exact values `riemannXi 0 = riemannXi 1 = 1/2` remain the
   boundary witnesses and are consistent with the new exact zero correspondence.
3. **Infinite analytic order.** If `analyticOrderAt riemannXi s = top`, xi vanishes in a
   neighborhood. The analytic identity theorem would make it globally zero, contradicting
   `riemannXi 1 = 1/2`. Lean proves `analyticOrderAt_riemannXi_ne_top` at every point.
4. **Hidden poles.** `riemannXiZeroDivisor_apply` identifies every divisor value with the integer
   cast of a natural analytic order, so the divisor is nonnegative and has no pole contribution.
5. **Support-only symmetry.** Lean transports analytic order through the affine map `s |-> 1-s`
   with derivative `-1`, proving equality of multiplicities rather than only equality of zero
   sets.
6. **Overclaim audit.** Local finiteness does not provide a canonical `Nat` enumeration,
   convergence of a zero sum, a Hadamard product, Li positivity, or RH. None is claimed.

## Compiled Results

New module: `LeanLab/Riemann/LiZeroDivisor.lean`.

- `riemannXi_ne_zero_of_one_lt_re`
- `riemannXi_ne_zero_of_isTrivialZeroPoint`
- `isNontrivialZero_iff_riemannXi_eq_zero`
- `analyticOrderAt_riemannXi_ne_top`
- `meromorphicOrderAt_riemannXi_ne_top`
- `riemannXiZeroMultiplicity`
- `riemannXiZeroMultiplicity_pos_iff`
- `riemannXiZeroDivisor`
- `riemannXiZeroDivisor_apply`
- `support_riemannXiZeroDivisor`
- `compact_inter_nontrivialZeros_finite`
- `analyticOrderAt_riemannXi_one_sub`
- `riemannXiZeroMultiplicity_one_sub`
- `riemannXiZeroDivisor_one_sub`

The key carrier theorem is

```lean
theorem support_riemannXiZeroDivisor :
    Function.support riemannXiZeroDivisor = {s : Complex | IsNontrivialZero s}
```

and each value is exactly

```lean
theorem riemannXiZeroDivisor_apply (s : Complex) :
    riemannXiZeroDivisor s = (riemannXiZeroMultiplicity s : Int)
```

## Literature Alignment

- Xian-Jin Li, 1997, DOI `10.1006/jnth.1997.2137`, defines the all-index derivative family whose
  positivity is RH-equivalent.
- Bombieri-Lagarias, 1999, DOI `10.1006/jnth.1999.2392`, gives zero-sum and Guinand-Weil
  formulations in which zeros are counted with multiplicity.
- This campaign supplies the project-side locally finite multiplicity carrier only. It does not
  reproduce their global zero sum or criterion.

## Verification

- `rtk lake env lean LeanLab/Riemann/LiZeroDivisor.lean`: pass, no warnings.
- `rtk lake build LeanLab.Riemann.LiZeroDivisor`: pass.
- `rtk lake env lean LeanLab/Riemann/TargetChecks.lean`: pass.
- `rtk lake env lean LeanLab/Riemann/AxiomsAudit.lean`: pass.
- Full `rtk lake build`: pass, 8620 jobs.
- Placeholder, explicit project declaration, `native_decide`, and resource-relaxation scans: empty.
- `rtk git diff --check`: pass.
- Audited new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Implementation commit `15e30c800e39d904b1623d5e8efcb40864e18655` is public on
`Ryugu-07/lean-lab-rh`. Lean Action CI run `29392983909`, build job `87280263113`, completed
successfully in 2m2s.

## Progress Accounting

Campaign classification: `BRIDGE_REDUCED`.

The fixed R3 divisor/local-multiplicity prerequisite is now closed, so `hard_gap_delta=1` for this
route-local DAG. The global RH assumption frontier is unchanged. Still open are order-one growth,
a global Hadamard product or substitute, a summable zero-side representation of every Li
coefficient, all-index positivity, and the exact Li/RH equivalence in Lean.

Next state: `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. Continuing R3 requires the audit to admit
a precise order-growth, canonical-product, or zero-summability edge; low-index Li calculations are
not admissible successors.
