# H6 Boyd Adjacent Puiseux and Jacobian Jump Loop 26 Preregistration

Date: 2026-07-20

Campaign: `PROOF-ATTEMPT-20260720-H6-BOYD-ADJACENT-PUISEUX-JUMP-01`

Mode: `PROOF-ATTEMPT`

Status: `LOCAL IMPLEMENTATION VERIFIED / PUBLIC IMPLEMENTATION CI PENDING`

## Opening

RH is the goal. This campaign attacks the first analytic-continuation layer of
`OBS-H6-BOYD-R2-POSITIVE-REAL-CONTOUR-01`. Loop 25 proved that the full Boyd--Nemes equation
`(15)` is equivalent to one exact positive-real contour equality, but it also proved that the
origin inverse available only on the first coordinate disk cannot justify the required contour
deformation. Loop 26 constructs the actual two-sheeted local continuation at both first adjacent
saddles and computes its inverse-Jacobian jump. The compiler decides every retained claim.

## Baseline and route selection

- `parent_commit`: `fc8a50b5a64fa5bb2d49fafb88289b80007c0585`.
- `baseline_public_ci`: Lean Action CI run `29733971984`, build job `88324814909`, passed in
  `2m30s` for the Loop 25 final ledger.
- `selected_node`: `OBS-H6-BOYD-R2-POSITIVE-REAL-CONTOUR-01`, directly upstream of
  `H6.debruijn-newman.boyd-r2-equation-15`, the effective `R2` estimate, and the Polymath
  Proposition 6.1 final-region certificate.
- `value_ranking`: retain H6-Q1. The missing adjacent-saddle branch structure is source-specific,
  now sharply isolated, and reuses the complete Loops 18--25 geometry. Repeating kernel
  integrability, Taylor coefficients, or centered-disk Cauchy estimates has lower value and is
  excluded.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active in every local outcome.

## Source audit and route ruling

- Boyd 1994, *Gamma function asymptotics by an extension of the method of steepest descents*,
  Proc. R. Soc. Lond. A 447, 609--630, DOI `10.1098/rspa.1994.0158`, derives the resurgence
  formulas cited as equations `(2.14)` and `(4.2)` by expanding the origin contour to adjacent
  saddles.
- Boyd 1995, *Approximations for the late coefficients in asymptotic expansions arising in the
  method of steepest descents*, Conditions 2.1 and equations `(9)`--`(15)`, makes the required
  branch and adjacent-contour geometry explicit.
- Nemes, arXiv `1310.0166`, equation `(15)`, records the exact target representation but cites
  Boyd for its derivation. Local TeX SHA-256:
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Paris, arXiv `1405.3423`, equations `(2.1)`--`(2.12)`, independently confirms that the inverse
  has branch points at the first adjacent critical images. Paris explicitly states that the
  equivalence of his Lagrange-remainder contour `(2.11)` with Boyd's remainder `(2.12)` was not
  proved. That equivalence is not a premise and cannot close this campaign.
- `route_ruling`: the source-faithful Lagrange/Binet route remains a fallback, but the current
  highest-value edge is the adjacent-saddle two-sheet certificate required by Boyd's own
  deformation.

## Fixed project objects

Use the existing definitions without replacement:

```text
h(u) = deBruijnNewmanPolymathBoydComplexSaddlePhase u = exp(u)-u-1,
a_n = deBruijnNewmanPolymathBoydComplexSaddlePoint n = 2*pi*i*n,
c_n = deBruijnNewmanPolymathBoydComplexSaddleImage n,
U(w) = deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w,
W(u) = deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u.
```

The already compiled identities include

```text
h(U(eta)) = eta^2/2                    for |eta| < 2*sqrt(pi),
h(a_n + v) = h(a_n) + h(v),
c_n^2/2 = h(a_n),
U'(0) = 1,
```

as well as the actual upper and lower origin-branch radial landings at `a_1` and `a_(-1)`.

## Exact mathematical target

For each `n in {1,-1}` and every local uniformizer `eta` with
`|eta| < 2*sqrt(pi)`, define the two adjacent sheets

```text
V_n^+(eta) = a_n + U(eta),
V_n^-(eta) = a_n + U(-eta).
```

Prove all of the following as one certificate.

1. Both sheets are analytic in `eta` and satisfy the same translated phase equation

   ```text
   h(V_n^+(eta)) = h(V_n^-(eta)) = h(a_n) + eta^2/2.
   ```

   The involution `eta -> -eta` exchanges the two sheets and is the local monodromy at the
   adjacent branch value.

2. On the punctured uniformizer disk, define the phase-Jacobians

   ```text
   K_n^+(eta) = U'(eta)/eta,
   K_n^-(eta) = -U'(-eta)/eta.
   ```

   Prove these are exactly the derivatives `dV_n^+ / d(h-h(a_n))` and
   `dV_n^- / d(h-h(a_n))`, in the precise chain-rule sense along the uniformizer map
   `eta -> h(a_n)+eta^2/2`.

3. Prove the exact jump and its leading singular coefficient:

   ```text
   K_n^+(eta) - K_n^-(eta) = (U'(eta)+U'(-eta))/eta,
   eta * (K_n^+(eta)-K_n^-(eta)) = U'(eta)+U'(-eta),
   lim_(eta->0, eta!=0) eta * (K_n^+(eta)-K_n^-(eta)) = 2.
   ```

4. Identify the actual Loop 24 origin branch near both endpoints. For the upper and lower radial
   paths, construct the translated local uniformizer by applying the actual global coordinate to
   `U_origin(w(t))-a_n`; prove eventually as `t -> 2*pi` from below that the translated point lies
   in the origin phase domain, the uniformizer lies in the coordinate disk and tends to zero,
   and

   ```text
   U_origin(w_n(t)) = V_n^+(eta_n(t))
   ```

   after the sign is fixed by the actual coordinate, not by choosing an arbitrary square root.
   The companion value `V_n^-(eta_n(t))` is then the certified second local sheet at the same
   phase value.

## Proposed Lean surface

Names may be adjusted for type-correct implementation, but the quantifiers and mathematical
content above are fixed.

```lean
def deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus
    (n : Int) (eta : Complex) : Complex :=
  deBruijnNewmanPolymathBoydComplexSaddlePoint n +
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta

def deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus
    (n : Int) (eta : Complex) : Complex :=
  deBruijnNewmanPolymathBoydComplexSaddlePoint n +
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)

def deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus (eta : Complex) : Complex :=
  deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta / eta

def deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus (eta : Complex) : Complex :=
  -deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta) / eta

theorem deBruijnNewmanPolymathBoydAdjacentPuiseux_phase
    {n : Int} (hn : n = 1 ∨ n = -1) {eta : Complex}
    (heta : eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n eta) =
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2 ∧
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n eta) =
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2

theorem deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_jump
    {eta : Complex} (heta : eta ≠ 0) :
    deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
        deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta =
      (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)) / eta

theorem tendsto_deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_regularizedJump :
    Tendsto
      (fun eta : Complex => eta *
        (deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
          deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta))
      (𝓝[≠] 0) (𝓝 2)
```

The final aggregate theorem must also contain the two actual radial-sheet identification
statements, not only the algebraic phase and jump formulas.

## Proof strategy fixed before editing

1. Prove the exact translation identity
   `h(a_n+v)=h(a_n)+h(v)` from `exp(a_n)=1` and combine it with the existing disk inverse phase
   theorem.
2. Package `V_n^+` and `V_n^-` as analytic functions on the actual open coordinate disk. Derive
   both eta-derivatives from the existing analyticity of `U`.
3. On `eta != 0`, divide the eta-derivatives by the derivative of `eta^2/2`. Prove the exact
   sheet-jump identity algebraically, then use continuity of `U'` and the compiled `U'(0)=1` for
   the punctured-limit coefficient `2`.
4. Use the Loop 24 radial landing limits and openness of the origin phase domain to show that the
   translated upper and lower contour points eventually enter that domain. Apply the actual
   global coordinate and its two-sided inverse to obtain the uniformizers, their convergence to
   zero, and exact actual-sheet identities.
5. Attempt to continue the companion sheets away from the endpoint along the source adjacent
   contours. If the attempt reaches the complete unbounded cut and supplies the integrable jump,
   use it immediately in the Loop 25 positive-real contour equality. Otherwise stop at the exact
   first theorem where global continuation, boundary decay, or contour homology is missing.

## Success, falsification, and meaningful partial

- `success_criterion`: compile an actual cut-plane continuation of the origin inverse Jacobian
  with both first adjacent boundary jumps and use it to prove
  `deBruijnNewmanPolymathBoydR2PositiveRealContourEquality`; Loop 25 then promotes this through the
  existing iff to the full right-half-plane Boyd--Nemes equation `(15)`.
- `minimum_hard_gap_reduction`: if global cut continuation does not compile, retain only the
  indivisible certificate consisting of both analytic Puiseux sheets, both exact phase-Jacobians,
  their exact jump and regularized coefficient, and actual upper/lower Loop 24 sheet
  identification. Algebraic translation, a phase-square identity, or the coefficient limit alone
  is insufficient.
- `falsification_criterion`: a compiled calculation shows that the translated phase, sheet
  involution, Jacobian orientation, actual radial sign, or singular coefficient differs from the
  fixed statements. Record the exact counterstatement and do not repair it by changing the
  source normalization.
- `local_stop`: stop when equation `(15)` is proved, a falsification theorem compiles, or the full
  minimum hard-gap reduction compiles and further continuation reaches a precise new obstruction
  requiring global cut topology, unbounded contour decay, or an independent source theorem.
  Local stop returns to value-ranked route selection and never pauses the persistent RH Goal.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes the disk-wide normalized inverse, its phase and
  Jacobian equations, `U'(0)=1`, its Cauchy series on every smaller disk, both actual radial
  landings, the positive-real actual-`R2` Gaussian-Jacobian identity, right-half-plane holomorphy,
  and the exact reduction of equation `(15)` to one positive-real contour equality.
- `still_open_before`: no adjacent Puiseux sheet or Jacobian jump is registered; no inverse
  continuation outside the first coordinate disk is available; the whole-real Gaussian contour
  cannot yet be deformed; equation `(15)`, effective `R2`, Table 1, H6-E/G8, and RH remain open.
- `anti_substitution`: do not assume a Lambert-W branch, monodromy theorem specialized to this
  phase, Boyd equation `(15)`, Paris `(2.11)=(2.12)`, a Binet/Stieltjes Gamma remainder, an
  exterior inverse, boundary decay, contour homology, or an effective `R2` bound.
- `conjecture_status`: no model-original conjecture is admitted as a premise. The Puiseux
  statements are direct consequences targeted for proof from already compiled project objects.

## Mechanical and publication gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentPuiseuxJump.lean`.
- Any retained spine must be imported and registered in `LeanLab/Riemann/Targets.lean`, receive
  name resolution and exact statement witnesses in `LeanLab/Riemann/TargetChecks.lean`, and have
  selected `#print axioms` entries in `LeanLab/Riemann/AxiomsAudit.lean`.
- At loop end update `attempts/h6_polymath_table_row_certificates.md`,
  `research/hard_gap_dag.md`, this preregistration outcome, and `HANDOFF.md`.
- No `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `unsafe`, or resource-limit
  relaxation.
- Run standalone diagnostics, exact witnesses, selected axiom audits, all forbidden scans,
  `git diff --check`, the full project build, and public implementation/evidence CI.
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 26
  Lean proof-source edit.

## Runtime disclosure

- `compaction_state`: Loop 26 begins after the third inherited compaction of Loop 25. After that
  recovery, canonical governance, `HANDOFF.md`, Targets/TargetChecks, the current attempt,
  hard-gap DAG, and the full Loop 25 preregistration were re-read before Loop 25 publication and
  this route selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: the persistent RH Goal remains active.

## Local outcome

- `result`: `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`.
- `success_criterion`: not met. The positive-real contour equality and Boyd--Nemes equation
  `(15)` remain open and were not used as premises.
- `minimum_hard_gap_reduction`: met as one aggregate Lean certificate. Both first-adjacent
  translated sheets are analytic, solve the same phase equation, are exchanged by `eta -> -eta`,
  have the exact chain-rule phase-Jacobians and jump, and satisfy the punctured regularized limit
  `eta * (K^+ - K^-) -> 2`. The actual upper and lower Loop 24 radial branches select the positive
  sheets through the compiler-defined global coordinate; their uniformizers tend to zero and are
  eventually nonzero.
- `compiled_endpoint`:
  `deBruijnNewmanPolymathBoydAdjacentPuiseuxJumpCertificate` proves
  `deBruijnNewmanPolymathBoydAdjacentPuiseuxJumpCertificateStatement`.
- `additional_continuation_probe`: the principal square-root uniformizer gives analytic positive
  and negative continuation candidates wherever its radicand lies in `Complex.slitPlane` and the
  uniformizer stays in the first coordinate disk. Both solve the exact original phase equation
  `h(V)=w^2/2` there.
- `boundary_contact`: Lean proves at `w=0`, for both `n=1` and `n=-1`, that the principal
  uniformizer has norm exactly `2*sqrt(pi)`, the boundary of the available open disk. Thus this
  first adjacent chart certificate alone does not supply continuation through the origin
  coordinate, much less over the whole unbounded real Gaussian contour.
- `new_obstruction`: `OBS-H6-BOYD-R2-GLOBAL-CUT-STITCHING-01`. Construct compatible adjacent or
  exterior inverse charts beyond the first disk, prove exact upper/lower cut boundary values and
  jumps, and certify the unbounded contour homology and decay needed by the Loop 25 equality.
- `assumption_frontier_after`: the local adjacent Puiseux sheets, their involution, phase laws,
  Jacobian jump, coefficient two, actual radial sign selection, and principal-chart boundary
  contact are K0 locally. No exterior inverse, global cut boundary value, contour deformation,
  equation `(15)`, effective `R2`, or Table 1 certificate is introduced.
- `classification_deltas`: `rh_frontier_delta=0`, `hard_gap_delta=1`,
  `route_infrastructure_delta=1`, `obstruction_map_delta=1`.
- `local_mechanical_audit`: 840-line production module, proven Target, eight exact
  TargetChecks, ten selected axiom prints, empty placeholder/custom-declaration/resource-limit
  scans, `git diff --check`, and the full 8,731-job build pass. Every selected declaration depends
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- `public_preregistration`: commit `92d945958e1f19ea139227e5226d3aae720e4c7a`, Lean Action run
  `29734964368`, build job `88328014471`, passed in `1m52s` before proof-source editing.
- `public_implementation`: pending commit and CI.
- `compaction_state_after`: two inherited compactions during Loop 26. After each, canonical
  governance, HANDOFF, Targets/TargetChecks, the current H6 attempt, hard-gap DAG, full
  preregistration, and relevant production certificate were re-read before further proof or
  publication work.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active.
