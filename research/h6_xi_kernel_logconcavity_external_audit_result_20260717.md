# H6 Xi-Kernel Log-Concavity External Lean Audit Result

Date: 2026-07-17

Campaign: `FALSIFICATION-20260717-H6-XI-LOGCONCAVITY-LEAN-01`

Status: `PUBLICLY_CLOSED`

## Pinned source

- paper v2: `10.20944/preprints202604.0159.v2`
- repository: `gershonavi/xi-log-concavity`
- commit: `7a89db1d546257d8dabefe1ac8b8d4769298a355`
- source toolchain: Lean `v4.29.0`

The v2 paper correctly states that TP2 does not imply the RH-equivalent TP-infinity condition.
The attached repository's README and formal proof surface are not aligned with that corrected
scope.

## Kernel-checked result

`XiKernelLogConcavityAudit.lean` reconstructs the external zero predicate and exact Hurwitz
proposition. The declaration omits every convergence and analyticity premise. Lean verifies the
counterexample

```text
F_n(z)=1,    G(z)=z-i.
```

Every `F_n` is zero-free, `G(0)!=0`, but `G(i)=0` and `Im(i)=1`. Therefore the exact external
Hurwitz schema is false. Lean also proves that the reconstructed external `IsLogConcaveOn` shape
holds for every function because the source definition concludes only `True`.

## External certification boundary

The pinned source contains thirteen explicit custom axioms. Its advertised full-kernel theorem
and analytic variant conclude `True`, not a derivative inequality. Both decisive perturbation
bounds are custom axioms of type `True`. The Python script encloses only the sum of terms
`n=1,...,5` on `[0,1/2]`, with no certified `n>=6` remainder, and checks the finite Region-B tail
only at `u=1/2` while assuming the required global decrease.

No external code is copied: the repository has no `LICENSE` file, notwithstanding the README's
MIT label.

## Audit

- new module: standalone diagnostic-free compile
- dedicated build: 782 jobs, success
- full build: 8,697 jobs, success
- exact TargetChecks: pass
- selected axioms: `propext`, `Classical.choice`, `Quot.sound`
- no `sorry`, `admit`, `native_decide`, custom axiom/constant/opaque/unsafe declaration, or resource
  relaxation in project edits

## Classification

`EXTERNAL_FORMALIZATION_REJECTED_AS_PREMISE`; `hard_gap_delta=0`,
`route_infrastructure_delta=0`. This does not refute actual Xi-kernel log-concavity and does not
change H6-E/G8 or RH. Implementation commit `8ecb002d1591ae93fbc23ba42c7a487c16c8beb5`
passed public Lean Action CI run `29550587517`, build job `87792042425`, in `1m50s`. Evidence
commit `131aff89283644bcabd2f620b94f99dc6ae30843` passed public CI run `29550788159`, build job
`87792636844`, in `1m55s`; the campaign is publicly closed.
