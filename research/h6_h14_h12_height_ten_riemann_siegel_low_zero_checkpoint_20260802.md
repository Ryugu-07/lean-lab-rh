# H6 x H14 x H12 Height-Ten Riemann--Siegel Low-Zero Checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-LOW-ZERO-01`

Status: `MEANINGFUL_PARTIAL / LOCAL_AUDIT_GREEN / SUBATTACK_ACTIVE /
GLOBAL_GOAL_ACTIVE`

## Historical purpose

This subattack re-enters the classical Riemann--Siegel low-zero route through the exact
Titchmarsh contour identity already formalized by the H6 de Bruijn--Newman work. On
`13/2<=y<=10`, the historical cutoff is `N=1`, so the full finite sum collapses to one residue.
The aim is to test whether this historical mechanism closes the H14 low-zero producer required
by the H12 Levinson--Montgomery height-ten certificate without extending isolated
Euler--Maclaurin endpoint tables.

This route was selected as omission search. It asks whether the source's phase-sensitive
remainder contains useful information that the project's earlier integrability majorant erased.
Independent conjecture proposals, falsification, and direct RH attacks remain open.

## Public gate

Docs-only preregistration commit `ea5bc3488daffbd38e1fdab2551d2cc7067b6713` passed Lean Action
run `30714195699`, build job `91406858114`, in `1m46s`. Production edits began only after that
gate passed.

## Compiled results

The new no-sorry module is
`LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelLowZero.lean`.

1. `riemannSiegel_criticalLine_eq_add_conj` proves the exact arbitrary-`N` critical-line
   conjugation formula for the two finite Riemann--Siegel halves.
2. `riemannSiegel_criticalLine_one_eq_prefactor_remainder_re` specializes to `N=1` and proves
   that `(1/8)*riemannXi(s)` is twice the real part of the single source prefactor plus the
   contour remainder.
3. `riemannXi_ne_zero_of_riemannSiegel_one_remainder_margin` proves that a strict real-part
   remainder margin forces xi nonvanishing.
4. `riemannZeta_criticalLine_ne_zero_thirteenHalves_ten_of_riemannSiegel` transports the literal
   uniform margin on `13/2<=y<=10` to actual zeta nonvanishing on that interval.
5. `speiserZetaDerivRatio_rightVertical_re_neg_thirteenHalves_ten_of_riemannSiegel` composes that
   nonvanishing with the already compiled Levinson--Montgomery archimedean sign to obtain the
   right-high quotient sign.
6. `norm_deBruijnNewmanRiemannSiegelRawIntegral_le_globalMajorant` evaluates the integral of the
   existing cancellation-free majorant in closed form.
7. `one_lt_riemannSiegel_globalMajorant_rhs_on_heightTenHigh` proves that this displayed
   upper-bound right side is strictly greater than `1` throughout the target interval.

The exact open premise is named `HeightTenRiemannSiegelOneRemainderMargin`. It is intentionally
visible and is not an axiom or an assumed theorem.

## Exact obstacle

The existing source-line estimate replaces the principal-power phase by the worst-case factor
`exp(abs(Im(s))*pi)`. This is appropriate for integrability and contour shifting, but it takes
absolute values before using the cancellation needed by the one-term low-height formula.

The proof that the resulting right side exceeds `1` has only this meaning: the current displayed
upper bound cannot directly certify the desired `<1`-scale margin. It is not a lower bound on the
actual contour remainder, does not show that the true remainder is large, and does not falsify
the Riemann--Siegel attack.

## Audit

- standalone module build: `8745/8745`;
- full project build: `8829/8829`;
- `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and `LeanLab.lean` pass with
  `-DwarningAsError=true`;
- seven selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- scans for `sorry`, `admit`, `native_decide`, custom axioms, `opaque`, `unsafe`, and relaxed
  resource options are empty;
- `git diff --check` is clean.

## Strict limits

The uniform remainder margin has not been proved. Therefore this checkpoint does not prove a new
actual low-height zero-free interval, an unconditional right-high vertical zone, the complete
height-ten boundary, `LevinsonMontgomeryHeightTenCertificate`, H12, or RH.

The other five vertical zones and the compact-middle top sign are independent open producers.
The subattack and parent campaign remain active.

## Next producer

Compare two source-faithful options before further code generation:

1. preserve the exact principal-argument phase in the current Titchmarsh source-line integral
   and derive a uniform bound for the real part rather than the integral norm;
2. reconstruct the classical Riemann--Siegel saddle/remainder expansion and formalize its first
   explicit low-height error term with a replayable uniform constant.

Selection should turn on which source theorem shortens the exact margin producer. It should not
optimize the endpoint `13/2`, extend isolated endpoint tables, or tune the already proved coarse
majorant.
