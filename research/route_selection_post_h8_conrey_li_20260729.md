# Route Selection after H8 Conrey--Li RKHS Shift

Date: 2026-07-29

Status: `RERANK_COMPLETE / H1_SELBERG_LOCAL_SIGN_CHANGE_SELECTED`

## Closed parent

Campaign `LITERATURE-20260729-H8-CONREY-LI-RKHS-SHIFT-01` is publicly closed at
`FULL_UPPER_HALF_PLANE_PRODUCER_SUCCESS`. Its final-ledger commit
`84de6e2d13431aa3069d5808b3018eb66f50ccd8` passed Lean Action run `30388546641`,
build job `90373923787`, in `1m52s`.

The campaign closes only the abstract upper-half-plane RKHS producer. The concrete actual-xi
space and positive shift, the second Hardy-RKHS continuation, H8, and RH remain open. Fresh
historical route selection is required.

## Census correction

The H0--H14 table is an audited family baseline, not an exhaustive list of human proof
mechanisms. In particular, H1 currently compresses three materially different methods:

1. Hardy--Littlewood real critical-line oscillation;
2. Selberg's 1942 sign-change method with a squared root mollifier;
3. Levinson--Conrey's argument-principle method with an inverse-zeta mollifier off the
   critical line.

The repository has theorem-producing campaigns for the first and third mechanisms. Selberg's
independent method appears only in prose. Treating H1 as a single covered row therefore hides
a genuine historical omission.

## Cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1-Selberg sign changes | Formalize the actual critical-line local sign-change detector after multiplication by the squared modulus of a root mollifier. | No production module, Target, or attempt reconstructs Selberg's independent method. The nonnegative square is the exact device preventing the mollifier from creating false sign changes. | **Select.** |
| H1 Levinson--Conrey | Formalize the principal zero-count inequality before the mollified mean value. | This is also source-important and is not a numerical optimization, but H1 already has several Levinson-shaped campaigns while Selberg has none. | Retain as the next H1 comparison candidate. |
| H2/H11 density and statistics | Find an actual-zeta statistic that cannot absorb a finite or sparse off-line orbit. | Existing normalized statistics permit persistent sparse exceptions; no source-backed amplifier is identified. | Retain open. |
| H7 spectral/trace | Construct an infinite arithmetic operator and a controlled trace identity. | Finite certificates compile, but the missing infinite producer remains broad. | Retain open. |
| H8 de Branges/RKHS | Construct the concrete xi RKHS shift or the second half-strip continuation. | The adjacent abstract producer has just closed; immediate continuation would be route inertia. | Retain open. |
| H10 function fields | Formalize actual curve intersection theory or a number-field transfer. | The lattice-to-real numerical hinge compiles, but the geometric producer remains unavailable. | Retain open. |
| H12 Speiser | Complete the multiplicity-aware global indented argument principle and top variation estimate. | Several local contour inputs compile; the remaining package is global and still valuable. | Retain open. |

## Historical source lock

The canonical source is:

Atle Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske Vid. Akad. Oslo,
No. 10 (1942), 1--59.

The method is independently distinguished from Levinson's method in the source-aligned
introduction of Conrey--Farmer--Kwan--Lin--Turnage-Butterbaugh,
*Short mollifiers of the Riemann zeta-function* (2025), arXiv:2508.11108. The historical
mechanism is also summarized in Henryk Iwaniec's lecture notes *The critical zeros -- 100%
sometimes*: on the critical line the mollifier is taken as a square `|N(s)|^2`, where `N`
models `1/sqrt(zeta)`, and sign changes of the resulting real function detect critical zeros.

This campaign does not use the later variational optimization of derivative combinations and
does not optimize a reported proportion.

## Omission probe

The source square has two distinct roles that paper prose can blur:

1. it is nonnegative on the critical line, so multiplying by it cannot reverse the sign of the
   Hardy coordinate;
2. it may vanish, so a zero of the mollified product alone need not be a zeta zero.

The safe detector is therefore not "the product has a zero." It is a strict two-sign
certificate, or an analytic condition strong enough to force both signs. The selected local
condition is

```text
abs (integral F) < integral (abs F)
```

on a nondegenerate interval. For a continuous real `F`, this strict triangle gap forces one
positive and one negative value. Since the squared root mollifier is nonnegative, the actual
Hardy-xi coordinate has opposite endpoint signs and hence an actual critical-line zero.

An arbitrary real or complex multiplier can manufacture a sign change while the base function
never vanishes. A compiled countermodel must preserve this distinction.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H1-SELBERG-LOCAL-SIGN-CHANGE-01`.
- `node`: `H1-SELBERG-LOCAL-SIGN-CHANGE-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: define a finite root mollifier and the actual mollified Hardy-xi coordinate;
  prove continuity, reality, and nonnegative-square sign preservation; prove the strict local
  integral-gap detector; turn it into an actual nontrivial zeta zero in the interval; assemble
  separated detected intervals into distinct zero witnesses; compile an arbitrary-multiplier
  false-sign-change control.
- `meaningful_partial`: the actual one-interval zeta-zero detector and negative control compile,
  while the finite separated-interval assembly is isolated as the first open edge.
- `strict_boundary`: no Selberg moment estimate, no lower bound for the measure or number of
  detected intervals, no `T log T` critical-zero count, no positive proportion, no H1 result,
  and no RH result.
- `production_gate`: no `LeanLab/` edit before the docs-only preregistration passes public CI.

The persistent RH Goal remains active.
