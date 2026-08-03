# Attempt Log: H12 Height-Ten Left Low/Middle Phase

Date: 2026-08-03

Campaign: `PROOF-ATTEMPT-20260803-H12-HEIGHT-TEN-LEFT-LOW-MIDDLE-PHASE-01`

Parent: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Global goal: active

| Step | Action | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_SELECTION` | Compared the left low/middle vertical, right low/middle vertical, compact-middle top, and broader historical frontiers. The left route already has unconditional actual-zeta nonvanishing and can use a phase handoff at height six. | Freeze `Re(q(iy))>0` on `[0,6]` and `Im(q(iy))<0` on `[6,13/2]`, where `q=zeta'/zeta`. |
| 2 | `FULL_PHASE_BACKEND` | Lean reconstructed the complete complex reflection identity, a quotient perturbation ball, twice-shifted complex archimedean enclosures, phase consumers, the exact zero endpoint, and a conditional complete-left join. | Continue to rational positive-width cells; the backend alone is below meaningful partial. |
| 3 | `MIDDLE_CELL_SELECTION` | Navigation showed a comfortable negative imaginary margin across `[6,13/2]`. No navigation decimal became a theorem premise. | Test the entire frozen middle interval as one cell centered at `25/4`, with Euler--Maclaurin cutoff `N=4`. |
| 4 | `FIXED_CENTER_POWER_TRANSPORT` | Exact binary-log, Taylor-exponential, and rounded complex-power bounds transported all four finite terms from the midpoint to every height in the cell. Lean proved value-center error at most `1/50000` and derivative-center error at most `1/25000`. | Reduce the finite quotient sign to rational polynomial inequalities. |
| 5 | `JOINT_BERNSTEIN_ATTEMPT` | A direct degree-20 Bernstein certificate for the combined quotient numerator had positive rational Bernstein coefficients, but normalization exceeded Lean's default heartbeat budget. No resource option was relaxed. | Record the certificate-shape failure and decompose the proof into lower-degree component bounds. |
| 6 | `COMPONENT_BERNSTEIN_REPAIR` | Separate exact Bernstein certificates proved `7/8<=Re(Z)<=19/20`, `-3/10<=Im(Z)<=-1/4`, `7/200<=Re(D)<=7/100`, and `27/200<=Im(D)<=4/25` for the finite centers. | Derive the finite center ratio imaginary part `<-1/8` and the exact finite Euler--Maclaurin quotient imaginary part `<-3/25`. |
| 7 | `ARCHIMEDEAN_PHASE` | An exact argument decomposition reduced the paired shifted archimedean imaginary part to `-(1/2)(atan(y/6)-atan(y/7))` plus a rational correction. Lean proved the angle gap at least `1/20`, the rational correction at most `-3/80`, and the paired term `<-3/50`. | Combine finite and archimedean centers before paying actual-function errors. |
| 8 | `ACTUAL_ERROR_TRANSFER` | Lean proved center imaginary part `<-9/50`, actual phase error at most `3/25`, value error at most `7/200`, derivative error at most `3/40`, and finite value norm at least `437/500`. | The strict phase margin survives on the complete frozen cell. |
| 9 | `MIDDLE_INTERVAL_CLOSURE` | Lean compiled `speiserZetaDerivRatio_leftVertical_im_neg_six_thirteenHalves` for every `6<=y<=13/2`. Exact TargetCheck and selected axiom prints pass. | Classify as the preregistered `meaningful_partial`: one complete frozen phase interval closes. |
| 10 | `NEXT_PRODUCER` | The remaining frozen producer is `Re(q(iy))>0` on `(0,6]`. Near zero, the reflected evaluator approaches the zeta pole and must expose cancellation before using an ordinary fixed center. | Keep the campaign and global RH Goal active; next compare pole-cancelled low cells with a local exact expansion at zero. |

## Current boundary

The 1702-line production module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftMiddleCell.lean` proves

```lean
theorem speiserZetaDerivRatio_leftVertical_im_neg_six_thirteenHalves
    {y : Real} (hy0 : 6 <= y) (hy1 : y <= 13 / 2) :
    (speiserZetaDerivRatio ((y : Complex) * Complex.I)).im < 0
```

The theorem is unconditional and uses no external zero table, sampled decimal, custom axiom,
`sorry`, `admit`, `native_decide`, resource relaxation, or opaque proof escape. The positive-real
interval `(0,6]`, the complete left edge, other height-ten boundary producers, the complete
height-ten certificate, H12, and RH remain open.

Implementation commit `a4ded06a39519fa1c37d0e97aef8e60a32eb33fb` passed public Lean
Action run `30819281694`, build job `91704779376`, in `3m51s`. The five proof and registration
blobs are frozen in immutable-evidence commit
`b084ee0599599dd16c278669071adca4465b9016`. Evidence run `30819751545`, build job
`91706377959`, passed in `2m42s`; every blob matches. The middle-cell subattack stops
successfully. The low phase producer, enclosing campaign, and global RH Goal remain active.
