# H6 Xi-Kernel Log-Concavity External Lean Audit Preregistration

Date: 2026-07-17

Campaign: `FALSIFICATION-20260717-H6-XI-LOGCONCAVITY-LEAN-01`

Mode: `FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_CI_PASSED_EVIDENCE_PENDING`

## Source lock

- paper: Avi Gershon, *On the Log-Concavity of the Riemann Xi Kernel*, preprint v2,
  DOI `10.20944/preprints202604.0159.v2`, posted 2026-06-29
- external repository: `https://github.com/gershonavi/xi-log-concavity`
- pinned commit: `7a89db1d546257d8dabefe1ac8b8d4769298a355`
- repository toolchain: Lean `v4.29.0`
- source grade before audit: `S3`; unreviewed source with an externally asserted Lean certificate
- reuse boundary: the repository has no `LICENSE` file although its README says `MIT`; no source
  code will be copied or vendored

## Claim separation

The v2 paper makes the mathematically correct scope distinction that strict log-concavity is
`TP2`, while RH requires the strictly stronger `TP-infinity` condition. This campaign does not
claim that log-concavity implies RH and does not attempt to refute actual log-concavity of the Xi
kernel.

The audit concerns only the external machine-verification claim. At the pinned commit:

1. `XiLogConcavity/Polya.lean` defines `IsLogConcaveOn K` with conclusion `True` and declares the
   cosine transform as an unconstrained custom axiom.
2. Its `hurwitz_theorem` omits analyticity and compact-uniform convergence entirely.
3. `tent_FT_real_zeros` has no tent-function premise and is a custom axiom.
4. `Basic.lean` gives `xi_kernel_log_concave` the proposition `True`; the tail ratio,
   perturbation, and full-kernel sign endpoints are also `True`.
5. `Analytic.lean` declares both decisive perturbation claims as custom axioms of type `True`, and
   its advertised full analytic endpoint again concludes only `True`.
6. `verify.py` sums only terms `n=1,...,5` on `[0,1/2]`; it supplies no bound for the omitted
   `n>=6` tail. On `[1/2,infinity)` it checks the same finite tail only at `u=1/2` and assumes the
   required global decrease.

The README still states the superseded claim that positivity and log-concavity imply an all-real
cosine transform, while the v2 paper explicitly says this implication is false in general.

## Exact mathematical falsification target

For a complex function define

```text
HasOnlyRealZeros(F) := forall z, F(z)=0 -> Im(z)=0.
```

The external Hurwitz axiom has the exact logical shape

```text
forall F : Nat -> Complex -> Complex, forall G : Complex -> Complex,
  (forall n, HasOnlyRealZeros(F n)) ->
  (exists z, G(z) != 0) ->
  HasOnlyRealZeros(G).
```

It is false. Take every `F_n` to be the constant function `1` and take `G(z)=z-i`. Every `F_n`
has no zeros, `G(0) != 0`, but `G(i)=0` and `Im(i)=1`.

The external log-concavity predicate has the exact logical shape

```text
forall t, 0 <= t -> forall Ksecond Kfirst, True,
```

and therefore holds for every function without expressing a derivative or inequality.

## Proposed Lean endpoint

Module: `LeanLab/Riemann/XiKernelLogConcavityAudit.lean`

```lean
def xiLogConcavityAuditHasOnlyRealZeros (F : Complex -> Complex) : Prop :=
  forall z, F z = 0 -> z.im = 0

def xiLogConcavityAuditHurwitzSchema : Prop :=
  forall (F : Nat -> Complex -> Complex) (G : Complex -> Complex),
    (forall n, xiLogConcavityAuditHasOnlyRealZeros (F n)) ->
    (exists z, G z != 0) ->
    xiLogConcavityAuditHasOnlyRealZeros G

theorem not_xiLogConcavityAuditHurwitzSchema :
    not xiLogConcavityAuditHurwitzSchema

theorem xiLogConcavityAudit_isLogConcaveOn_trivial
    (K : Real -> Real) :
    forall t, 0 <= t -> forall Ksecond Kfirst : Real, True

theorem xiKernelLogConcavityExternalAudit_endpoint :
    (forall K : Real -> Real,
      forall t, 0 <= t -> forall Ksecond Kfirst : Real, True) and
    not xiLogConcavityAuditHurwitzSchema
```

The names are project-local reconstructions of the exact external proposition shapes; the
external code is not imported.

## Success and rejection criteria

Success requires all of the following:

- the constant-sequence/linear-target counterexample compiles in Lean without custom axioms;
- an exact TargetChecks witness fixes the schema and counterexample, not only a theorem name;
- the transitive axiom audit contains only the accepted Lean/mathlib trust base;
- the external source scan, finite-truncation boundary, version mismatch, and license boundary are
  recorded;
- the result is classified only as rejection of the external Lean certification chain.

Reject or stop the campaign if the pinned source actually contains the omitted convergence and
analytic hypotheses, a nontrivial derivative-based log-concavity predicate, or a checked full
infinite-tail theorem. None was found in the pre-proof audit.

## DAG position and strength

- DAG node: H6-E/G8 source-shape reconnaissance
- relation to RH: the false external schema is not a valid RH implication; the true TP2 statement
  is strictly weaker than RH according to the source's corrected v2 scope
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open
- expected `hard_gap_delta`: 0
- expected `route_infrastructure_delta`: 0
- expected result: `EXTERNAL_FORMALIZATION_REJECTED_AS_PREMISE`

## Nearest attempts and material difference

The nearest project attempts are `OBS-H6-POSITIVE-COSH-LI3-01`, which rejects generic positive
moment extrapolation, and the completed H6-X4 heat-Li criterion, which identifies all-index
positivity with the actual open endpoint. This audit is materially different: it checks a human
source's claimed Lean certificate for a theta-specific shape theorem and its proposed TP2 bridge.
It does not construct another generic heat model and does not extend finite Li coefficients.

## Stop boundary

After the exact formal schema is falsified and the source evidence is logged, stop this campaign.
Do not silently expand it into a proof of full Xi-kernel log-concavity. A later campaign may attack
that theorem only after a fresh preregistration with an actual definition of `Phi`, complete
infinite-tail bounds, and a nontrivial derivative statement.

## Local outcome

The preregistration commit `def8b00d309ef5acc6a0f44a7eb0b47c0db25b01` passed public Lean
Action CI run `29549982781`, build job `87790283637`, in `1m32s` before proof-source edits.

`XiKernelLogConcavityAudit.lean` now compiles the exact constant-sequence/linear-target
counterexample, proves that the reconstructed external log-concavity predicate holds for every
function, and bundles both facts in `xiKernelLogConcavityExternalAudit_endpoint`. Exact
TargetChecks and all three selected transitive axiom prints pass; the latter contain only
`propext`, `Classical.choice`, and `Quot.sound`. Forbidden scans are empty and the full 8,697-job
build succeeds.

Local classification is `EXTERNAL_FORMALIZATION_REJECTED_AS_PREMISE`, with `hard_gap_delta=0`
and `route_infrastructure_delta=0`. Actual Xi-kernel log-concavity remains unverified by this
project and unrefuted; H6-E/G8 and RH remain open. Implementation commit
`8ecb002d1591ae93fbc23ba42c7a487c16c8beb5` passed public Lean Action CI run `29550587517`, build
job `87792042425`, in `1m50s`; immutable evidence closure remains pending.
