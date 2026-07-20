# H6 Boyd R2 Jacobian Remainder Loop 25 Preregistration

Date: 2026-07-20

Campaign: `PROOF-ATTEMPT-20260720-H6-BOYD-R2-JACOBIAN-REMAINDER-01`

Mode: `PROOF-ATTEMPT`

Status: `MEANINGFUL PARTIAL / HARD GAP REDUCED / PUBLIC IMPLEMENTATION CI PENDING`

## Opening

RH is the goal. This campaign directly re-enters the still-open Boyd--Nemes equation `(15)` at
`N=2`. It may close the complete equation, or it may expose the first exact contour obstruction
after compiling a mathematically substantive prefix. Successful theorems and precisely recorded
failed mechanisms are both project assets. The compiler decides every claim.

## Selection rationale

- `selected_node`: `H6-Q1`, specifically
  `H6.debruijn-newman.boyd-r2-equation-15`.
- `why_now`: Loop 12 proved both source-exact ray kernels integrable but lacked a global saddle
  inverse. Loops 13--16 now give the exact positive-real scaled-Gamma saddle integral and global
  real inverse. Loops 17--24 give the analytic complex inverse on the full first coordinate disk,
  its Cauchy Jacobian series, exact adjacent radial landings, and the unconditional first
  singularity radius `2*sqrt(pi)`.
- `value`: equation `(15)` is the missing exact representation upstream of the effective `R_2`
  bound used by the Polymath Proposition 6.1 final-region certificate.
- `route_choice`: the first proof move is to rewrite the project's actual `R_2(x)` on `x>0` as a
  normalized Gaussian integral of the real inverse-Jacobian remainder. The attack then tries to
  extract the two adjacent singular contributions and identify them with the already compiled
  Boyd ray kernels before extending from the positive real axis to `Re z>0`.

## Fixed source objects

Use the existing project definitions without replacement:

```text
GammaStar(z) = deBruijnNewmanPolymathScaledGamma z,
R2(z) = deBruijnNewmanPolymathGammaStirlingR2 z,
B2(z) = deBruijnNewmanPolymathBoydR2Integral z,
h(u) = exp(u)-u-1,
w(u)^2/2 = h(u),
U_R = deBruijnNewmanPolymathBoydRealSaddleInverse,
U = deBruijnNewmanPolymathBoydNormalizedCoordinateInverse.
```

The real saddle theorem already compiles, for `x>0`,

```text
GammaStar(x) = sqrt(x/(2*pi)) * integral_R U_R'(w)*exp(-x*w^2/2) dw.
```

The subtraction polynomial fixed by the normalized inverse germ is

```text
P2(w) = 1 - w/3 + w^2/12.
```

The odd term integrates to zero and the normalized Gaussian second moment is `1/x`, so the
intended exact real-axis prefix is

```text
R2(x) = sqrt(x/(2*pi)) * integral_R (U_R'(w)-P2(w))*exp(-x*w^2/2) dw.
```

## Exact success target

For every `z : C` with `0 < Re z`, prove the actual project equality

```text
R2(z) = B2(z).
```

Equivalently, compile the source-exact `N=2` specialization

```text
R2(z)
  = (1/(2*pi*i)) * (i^2/z^2)
      * integral_(0,infinity)
          s*exp(-2*pi*s)*GammaStar(i*s)/(1-i*s/z) ds
    - (1/(2*pi*i)) * ((-i)^2/z^2)
      * integral_(0,infinity)
          s*exp(-2*pi*s)*GammaStar(-i*s)/(1+i*s/z) ds.
```

The equality must use the existing `B2` definition, whose two kernels and signs were already
checked in Loop 12.

## Proposed Lean declarations

Names may be adjusted for type-correct implementation, but the promoted mathematical content and
quantifiers are fixed.

```lean
def deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand
    (x w : R) : R :=
  (deriv deBruijnNewmanPolymathBoydRealSaddleInverse w -
      (1 - w / 3 + w ^ 2 / 12)) * Real.exp (-x * w ^ 2 / 2)

theorem deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand_integrable
    {x : R} (hx : 0 < x) :
    Integrable (deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x)

theorem deBruijnNewmanPolymathGammaStirlingR2_ofReal_eq_boydJacobianRemainder
    {x : R} (hx : 0 < x) :
    deBruijnNewmanPolymathGammaStirlingR2 (x : C) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        integral (deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x) : R) : C)

theorem deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_integrals
    {z : C} (hz : 0 < z.re) :
    deBruijnNewmanPolymathGammaStirlingR2 z =
      deBruijnNewmanPolymathBoydR2Integral z
```

The implementation should also expose exact normalized Gaussian zeroth, first, and second moment
lemmas if they are used transitively, and should certify the coefficients `1`, `-1/3`, `1/12`
from the actual inverse germ rather than merely selecting a polynomial whose integral happens to
produce `1+1/(12*x)`.

## Proof strategy fixed before editing

1. Prove integrability and the normalized Gaussian moments at parameter `x>0`.
2. Subtract `P2` from the compiled Loop 16 Gaussian-Jacobian integral and derive the exact
   project `R2(x)` identity above. Prove the first three inverse-Jacobian coefficients from the
   normalized saddle equation or the actual local inverse germ.
3. Identify the real inverse/Jacobian with the restriction of the Loop 23/24 complex inverse on
   the first disk. Express the Jacobian remainder by its Cauchy representation on every smaller
   circle.
4. Deform the real coordinate contour to the two adjacent radial boundaries justified by Loop 24.
   Compute the two boundary contributions at the `+/-2*pi*i` saddles and match their changes of
   variable with the existing positive and negative Boyd kernels, including every orientation,
   `i^2`, and denominator sign.
5. Prove the resulting equality first for positive real `z`. Prove both sides analytic on the
   connected right half-plane and use the identity theorem to obtain the exact success target.

## Success, falsification, and local stop

- `success_criterion`: the exact all-right-half-plane equation `(15)` theorem compiles, with exact
  Targets/TargetChecks, selected standard-only axiom prints, forbidden scans, full build, and
  public implementation/evidence CI.
- `falsification_criterion`: a compiled calculation shows that the project normalization, source
  signs, inverse-germ coefficients, adjacent-contour orientations, or domain of validity differ
  from the displayed equation; or a required integral is not defined under the stated hypotheses.
- `meaningful_partial_criterion`: if the complete contour deformation does not compile, retain
  only a prefix that includes the exact actual-project real-axis `R2` inverse-Jacobian remainder,
  the certified subtraction coefficients, and a precise theorem-level statement of the first
  missing contour equality. Gaussian moments, Taylor coefficients, integrability, or new
  definitions alone do not count as loop progress.
- `local_stop`: stop this campaign when the full equation is proved, a falsification witness
  compiles, or the first genuinely external contour theorem remains after both the adjacent-ray
  deformation and a source-faithful Lagrange/Binet reconstruction have been attempted. A local
  stop returns to value-ranked route selection and never pauses the persistent RH Goal.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes both actual Boyd kernels and their integrability for
  `Re z>0`; the exact positive-real scaled-Gamma Gaussian-Jacobian integral; the global real
  saddle diffeomorphism; the disk-wide complex inverse and Jacobian; its Cauchy series on every
  smaller disk; both adjacent radial landings; and the exact maximal centered radius.
- `hard_gap_before`: no theorem equates the project's actual `R2` to the inverse-Jacobian remainder,
  no theorem extracts adjacent singular contributions from that remainder, and equation `(15)`
  remains only an open proposition definition.
- `anti_substitution`: do not assume equation `(15)`, a Binet/Stieltjes remainder formula, an
  effective `R2` estimate, an abstract remainder predicate, a hidden contour-decay hypothesis, or
  equality of two alternative remainder contours.
- `conjecture_status`: no model-original conjecture is admitted as a premise.

## Material difference from Loop 12

Loop 12 could only prove ray-kernel integrability and define the source RHS. It stopped because no
global saddle inverse or resurgence contour was available. Loop 25 starts with the now-compiled
global real and complex inverses, exact Cauchy radius, first adjacent singularities, and both
landing paths. The re-entry therefore attacks a different proof state and a concrete contour
identity, not the already exhausted denominator-majorant mechanism.

## Source alignment

- G. Nemes, arXiv `1310.0166`, equation `(15)`; local TeX SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- W. G. C. Boyd, *Gamma function asymptotics by an extension of the method of steepest descents*,
  Proc. R. Soc. Lond. A 447 (1994), 609--630, DOI `10.1098/rspa.1994.0158`.
- R. B. Paris, arXiv `1405.3423`, especially equations `(2.1)`, `(2.2a)`, `(2.3b)`, and the quoted
  Boyd remainder; downloaded source SHA-256
  `9234f701f5ae823f53a5947dcc2fe13a8209a5c28d7a6f91c8fd2a43665726c5`.
- Paris explicitly states that equivalence of his alternative contour expression `(2.5)` with
  Boyd's expression `(2.6)` was not proved and was only numerically supported. That equivalence is
  not a premise and cannot satisfy any success criterion here.

## Lean surface and mechanical gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydR2JacobianRemainder.lean`.
- On success or meaningful partial progress, update exact imports and witnesses in
  `LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`, and
  `LeanLab/Riemann/AxiomsAudit.lean`.
- At loop end update `attempts/h6_polymath_table_row_certificates.md`,
  `research/hard_gap_dag.md`, and `HANDOFF.md`.
- No `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`, or resource-limit
  relaxation.
- Every promoted theorem must compile independently and receive an exact statement witness and
  selected `#print axioms` inspection.
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 25
  Lean proof-source edit.

## Baseline and runtime

- `parent_commit`: `532ed31c2a74a368b4f5abb6aed9bf119b169d9f`.
- `baseline`: Loop 24 final-ledger CI run `29727990498`, build job `88305445443`, passed in
  `1m28s`.
- `governance_check`: `/Users/karasuakamatsu/Downloads/RH_GOVERNANCE_V4_PATCH.zip` has SHA-256
  `95820ea9624685c1e272889b159a49e98adc67844219bbaf3083b77b5e59550d`, exactly matching the
  existing import record. The Downloads and repository V4.1 directives also have identical
  SHA-256 `1cdab9113228051a920e9ec4d334cea41e56666508884d3cafbdc83b8599d6c3`.
- `compaction_state`: one inherited summary arrived during Loop 25 source audit. The canonical
  governance, `HANDOFF.md`, Targets/TargetChecks, current attempt, hard-gap DAG, Loop 12 and Loop
  24 preregistrations, relevant production sources, and exact primary-source formulas were re-read
  before this selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active.

## Next decision

- `next_if_success`: attack the effective uniform `R2` bound and then discharge the existing
  Polymath Proposition 6.1 final-region premise.
- `next_if_partial`: register the exact contour obstruction, retain only the meaningful compiled
  prefix, and compare the adjacent-ray route with a source-faithful Binet reconstruction before
  route selection.
- `global_goal`: the persistent RH Goal remains active in every local outcome.

## Loop 25 local outcome

- `result`: `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`. The complete Boyd--Nemes equation `(15)`
  was not proved and remains open.
- `compiled_positive_real_prefix`: for every `x>0`, the actual project
  `deBruijnNewmanPolymathGammaStirlingR2 (x:C)` is exactly the normalized Gaussian integral of
  `deriv U_R(w) - (1-w/3+w^2/12)`. The integrand is proved integrable.
- `coefficient_certificate`: Lean differentiates the actual inverse equation
  `(exp(U)-1)*U'=w` at zero and proves `U'(0)=1`, `U''(0)=-1/3`, and `U'''(0)=1/6`; hence the
  subtraction polynomial is exactly the degree-two Taylor polynomial of the inverse Jacobian.
- `holomorphy_prefix`: both Boyd kernels are rewritten as Stieltjes kernels. Their parameter
  derivatives are dominated locally by an integrable multiple of
  `s^(3/2)*exp(-pi*s)`. Lean proves the two ray integrals, the complete Boyd RHS, and the actual
  project `R2` differentiable on `Re z>0`.
- `exact_reduction`: the identity theorem compiles a strict equivalence between the complete
  all-right-half-plane equation `(15)` and one positive-real contour equality. Conjugacy reduces
  that equality further to a single real scalar identity involving the imaginary part of the
  positive Boyd ray.
- `first_missing_theorem`: `deBruijnNewmanPolymathBoydR2PositiveRealContourEquality`. It asks for
  equality of the compiled whole-real inverse-Jacobian Gaussian remainder and the compiled Boyd
  two-ray expression, with no hidden contour or decay premise.
- `adjacent_ray_attempt`: the compiled complex inverse and its Cauchy Jacobian are available only
  on the first coordinate disk. The whole-real Gaussian integral uses every real coordinate.
  Radial landing at the two boundary saddles does not supply analytic continuation on the exterior
  cut plane or the two boundary jump formulas, so a contour deformation cannot yet be stated from
  the available K0 interface without introducing the missing conclusion as a premise.
- `binet_attempt`: a source-faithful inventory found Euler's Gamma integral in mathlib but no
  Binet/Stieltjes Stirling-remainder formula. Reapplying the Euler integral and the compiled saddle
  changes of variables returns the already proved Jacobian remainder; it does not produce the
  Boyd ray jumps. No alternative-contour equivalence from Paris is used.
- `new_obstruction`: `OBS-H6-BOYD-R2-POSITIVE-REAL-CONTOUR-01`, requiring a cut-plane analytic
  continuation and adjacent-saddle jump certificate for the inverse Jacobian, or an independently
  formalized source-faithful Binet representation proving the same scalar equality.
- `classification_deltas`: `rh_frontier_delta=0`, `hard_gap_delta=1`,
  `route_infrastructure_delta=1`, `obstruction_map_delta=1`.
- `local_mechanical_audit`: 1,125-line production module, nine exact TargetChecks, eight selected
  standard-only axiom prints, three empty forbidden scans, `git diff --check`, and the full
  8,730-task build pass. Selected declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `compaction_state`: two inherited summaries occurred during Loop 25. After each, canonical
  governance, `HANDOFF.md`, Targets/TargetChecks, the current attempt, hard-gap DAG, and this
  preregistration were re-read before further proof or publication work.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active.
- `public_implementation`: pending.
- `public_closure`: pending.
