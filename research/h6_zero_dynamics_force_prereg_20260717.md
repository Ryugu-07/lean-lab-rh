# H6 Zero-Dynamics Force Preregistration

Date: 2026-07-17

Campaign: `PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01`

Mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED`

## Route selection

Fresh value-ranked selection follows the public closure of H6-H2d. The project now has the exact
source-normalized heat family, its backward heat equation, an order-one genus-one Hadamard
factorization with multiplicity, closed and forward-preserved good times, quantitative strip
contraction, and the unconditional good time `t=1/2`.

The alternatives were ranked as follows.

- H1-B and H2-B finite-height counts are useful infrastructure but cannot exclude one off-line
  zero and have lower immediate value.
- H6-Q (`Lambda <= 1/5`) needs a new certified saddle-point and interval-arithmetic stack and still
  stops short of the time-zero endpoint.
- W2/G7 and M2/G3 remain direct RH-equivalent targets, but the recorded prime-kernel,
  projection, sparse-frame, and ladder obstructions currently supply no materially new attack
  angle.
- H6 zero dynamics directly studies the only possible loss of real-rootedness when continuing
  from the compiled good time `1/2` toward `0`. Its first exact source theorem can reuse both the
  compiled heat PDE and the multiplicity-bearing Hadamard product.

Select a direct H6-E/G8 proof attempt. The attack begins by kernel-checking the regularized
infinite zero-force identity at a simple zero, then uses it to study collision exclusion while
moving backward in time. A finite polynomial force law, a merely conditional RH reformulation,
or a threshold-definition wrapper is not campaign success.

## Exact target

The campaign target is the unconditional time-zero statement

```lean
theorem deBruijnNewmanAllZerosReal_zero :
    deBruijnNewmanAllZerosReal 0
```

which is already compiled as equivalent to `Mathlib.RiemannHypothesis` but is not proved.

The first fixed proof spine is the source zero-dynamics identity. For

`Z_t = Complex.Hadamard.divisorZeroIndex₀ (deBruijnNewmanH t) univ`,

write `r_p` for the value of a divisor index and define the absolutely regularized force at a
nonzero zero `r` by

`1/r + sum' p, if r_p=r then 0 else (1/(r-r_p)+1/r_p)`.

At a simple zero `r` the required identity is

`H_t''(r) / (2*H_t'(r)) = regularizedForce(t,r)`.

Consequently, every differentiable real zero path `x(t)` through a simple zero satisfies

`x'(t) = 2*regularizedForce(t,x(t))`.

This is the divisor-indexed, absolutely convergent form of the principal-value equation in
Rodgers-Tao, Theorem 4.1. It is a required first spine theorem, not the final success criterion.

## Proposed Lean interface

Names and binder order may change, but the mathematical strength may not be weakened.

```lean
noncomputable def deBruijnNewmanRegularizedZeroForce (t : ℝ) (r : ℂ) : ℂ :=
  1 / r +
    ∑' p : Complex.Hadamard.divisorZeroIndex₀
        (deBruijnNewmanH t) (Set.univ : Set ℂ),
      if Complex.Hadamard.divisorZeroIndex₀_val p = r then 0
      else 1 / (r - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p

theorem summable_deBruijnNewman_regularizedZeroForceTerm (t : ℝ) (r : ℂ) :
    Summable (fun p => if Complex.Hadamard.divisorZeroIndex₀_val p = r then 0 else
      1 / (r - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)

theorem deBruijnNewmanH_second_deriv_div_two_deriv_eq_regularizedZeroForce
    {t : ℝ} {r : ℂ}
    (hr : deBruijnNewmanH t r = 0)
    (hsimple : deriv (deBruijnNewmanH t) r ≠ 0) :
    deriv (deriv (deBruijnNewmanH t)) r /
        (2 * deriv (deBruijnNewmanH t) r) =
      deBruijnNewmanRegularizedZeroForce t r
```

The path theorem may initially be stated for an already differentiable complex-valued path. A
later loop must construct and order local real paths from simple real zeros before the campaign
can claim the full Rodgers-Tao dynamics interface.

## Fixed attack architecture

1. Remove the full multiplicity fiber over `r` from the divisor canonical product. Prove the
   complement genus-one logarithmic derivative at `r`, including summability and nonvanishing.
2. Use `hsimple` to prove that the fiber cardinality is exactly one. Split the global canonical
   product into its one fiber factor and complement product.
3. Rewrite the one genus-one factor exactly as
   `(z-r) * (-exp(z/r)/r)` and combine it with the already constant Hadamard prefactor.
4. Differentiate the resulting global factorization twice at `r`. The quotient left after
   removing `(z-r)` has logarithmic derivative equal to `1/r` plus the complement sum.
5. Combine the ratio theorem with `partial_t H_t = -partial_z^2 H_t` and the chain rule along a
   differentiable zero path. Audit the sign and factor two against the source convention.
6. Build local real zero trajectories from the implicit-function theorem at simple real zeros,
   then relate collision-free continuation toward time zero to H6-E.
7. Attempt a theta-specific a priori bound strong enough to prevent finite-time collisions on
   `[0,1/2]`. No generic heat-flow or symmetry-only premise may be substituted: the compiled
   reverse-heat Li countermodel already rules out that mechanism.

Steps 1-5 are the first formalization loop. Steps 6-7 carry the genuinely open content. If the
collision estimate cannot be proved, record its exact quantified form and the first failed
inequality as an obstruction rather than treating the force identity alone as RH progress.

## Adversarial checks

- A simple zero has analytic order and divisor-fiber cardinality exactly one; merely assuming
  `H_t(r)=0` is insufficient.
- The fiber term contributes `1/r`, not zero. This is the logarithmic derivative of
  `-exp(z/r)/r` after removing `(z-r)`.
- The complement sum must be genuinely summable, not assigned a conditionally ordered value.
- The ODE sign is fixed by `partial_t H_t=-H_t''`: differentiating `H_t(x(t))=0` gives
  `x'(t)=H_t''(x(t))/H_t'(x(t))`.
- Repeated zeros, the collision time, and the endpoint `t=0` may not be silently excluded.
- Principal-value notation from an ordered real-zero enumeration may be used only after Lean
  proves its equality with the divisor-regularized sum.
- A theorem conditional on `deBruijnNewmanAllZerosReal 0`, RH, a uniform gap lower bound, or the
  desired collision exclusion is circular and cannot close the campaign.
- The actual theta-kernel family must be used for the open collision estimate; finite-dimensional
  heat polynomials are only falsification models.

## Sources and boundary

- B. Rodgers and T. Tao, *The de Bruijn-Newman constant is non-negative*, arXiv `1801.05914v5`,
  especially Theorem 4.1 and equation (5), records simple-zero trajectories and
  `partial_t x_k = 2 sum'_{j != k} 1/(x_k-x_j)` for `Lambda<t<=0`.
- G. Csordas, W. Smith, and R. S. Varga, *Lehmer pairs of zeros, the de Bruijn-Newman constant,
  and the Riemann hypothesis*, Constructive Approximation 10 (1994), 107-129, is the dynamics
  source used by Rodgers-Tao.
- The open collision-exclusion direction is not claimed by these sources. Proving it through
  time zero would prove RH.

The force identity is known mathematics reconstructed in Lean. Any new theta-specific collision
bound will receive a separate conjecture and novelty audit before an originality claim.

## DAG and accounting

- `node_id`: H6-E
- `gap_id`: G8
- `relation_to_RH`: exact RH endpoint
- `assumption_frontier_before`: H6-B, H6-H1, H6-H2a through H6-H2d, source order one, constant
  Hadamard factorization, closedness, forward preservation, and the good witness `t=1/2`
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH are open
- `nearest_project_attempt`: H6-H2d supplies strip contraction but leaves width `1` at time zero;
  OBS-H6-REVERSE-HEAT-LI-01 shows that generic backward Li transfer is false
- `new_attack_angle`: replace backward sign transfer by an exact multiplicity-aware zero-force
  law and seek theta-specific collision exclusion
- `expected_hard_gap_delta`: 1 only if the unconditional time-zero theorem compiles; otherwise 0
- `expected_route_infrastructure_delta`: 1 if the full source force/path interface compiles

## Success, falsification, and stop conditions

- `success_criterion`: `deBruijnNewmanAllZerosReal_zero` compiles without new nonstandard axioms;
  exact TargetChecks, axiom audit, forbidden scans, full build, and public CI pass.
- `first_spine_criterion`: the regularized force summability, simple-zero ratio, and path velocity
  compile with exact statement witnesses and standard-only axioms. This advances the attack but
  does not close it.
- `falsification_criterion`: a fixed algebraic sign, factor, summability, multiplicity, or source
  normalization clause in the force identity is false. Record a kernel-checked counterexample or
  contradiction.
- `obstruction_criterion`: after the dynamics interface compiles, the attack reduces to a precise
  unproved collision/gap estimate with no theta-specific derivation. Record it as an OBS node and
  return to route selection; do not weaken the final target.
- `local_stop`: only proof, falsification, or a precise obstruction stops this campaign. Any local
  stop leaves the persistent RH Goal active.

No Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Public preregistration gate

Preregistration commit `4405d60c2a33444f8ae43f2406631cc80faff356` passed public Lean Action CI
run `29532612360`, build job `87736257748`, in `2m29s`. Lean proof-source edits may now begin
against the fixed target and architecture above.

## Implementation loop 1 local result

The fixed first spine compiles in `DeBruijnNewmanDynamics.lean`. The implementation removes the
full zero fiber from the genus-one product, proves absolute summability of the regularized force,
recovers the simple removed factor, and proves the exact derivative ratio. Joint continuity of
both source moments then supplies a strict real Frechet derivative on `R x C`; the resulting chain
rule and backward heat equation prove the differentiable simple-zero path velocity with the fixed
positive sign and factor two.

The standalone module, exact Targets and five TargetChecks, five standard-only axiom prints,
forbidden scans, and `git diff --check` pass. The full 8,691-job build succeeds locally.
`hard_gap_delta=0` and `route_infrastructure_delta=1`: this is the known first-spine interface,
not collision exclusion or RH. The campaign remains active at steps 6-7.

## Public implementation gate

Implementation commit `ce65db1c0379a4accfef579c9e8c08995662dc19` passed public Lean Action CI
run `29534356022`, build job `87741989620`, in `2m36s`. The first spine is now public and may be
used by the next loop. The campaign remains active at local trajectory construction; H6-E/G8 and
RH remain open.

## Implementation loop 2 local result

The product-domain implicit-function step now compiles. Every simple real zero has a locally
unique differentiable zero trajectory; conjugation plus uniqueness makes it real in a time
neighbourhood, and two distinct anchors give locally ordered trajectories. The velocity theorem
has been strengthened to the neighbourhood-local zero hypothesis required by this construction.

The gap calculation is also explicit. The implementation removes both complete simple-zero
fibers, proves the pair remainder absolutely summable, and derives

`force(t,s)-force(t,r)=2/(s-r)+pairRemainder(t,r,s)`.

For real anchored paths Lean then proves

`(gap^2)'=8+4*gap*Re(pairRemainder)`.

The exact module, two Targets, eleven campaign TargetChecks, twelve campaign axiom prints, empty
forbidden scans, `git diff --check`, and the 8,691-job full build pass locally. Every selected
declaration has only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
`hard_gap_delta=0` and campaign-level `route_infrastructure_delta=1` remain unchanged.

The next mathematical attack is no longer local path construction. It is a theta-specific,
height-aware integrated control of the pair-removed remainder strong enough to continue all
relevant real zero pairs from the good time `1/2` to time `0`, together with treatment of the
first possible repeated zero. No fixed positive height-uniform gap premise is admitted.

## Public loop-2 implementation gate

Implementation commit `03ce2ac2ee68b7d9a6d48d56aed37ab40836c30d` passed public Lean Action CI
run `29536815968`, build job `87750004173`, in `1m54s`. Local real path construction, pair
ordering, the pair-removed force decomposition, squared-gap evolution, exact Targets/TargetChecks,
and the standard-only axiom audit are now public and may be used by the next attack loop.
