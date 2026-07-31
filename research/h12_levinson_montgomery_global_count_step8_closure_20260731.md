# H12 Levinson--Montgomery Global Count Step 8 Closure Ledger

Date: 2026-07-31

Campaign:
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`

Closed subnode:
`H12.speiser.levinson-montgomery-log-count-and-base-reduction`

Open parent:
`H12-LM-GLOBAL-INDENTED-COUNT-01`

Status: `CLOSURE_LEDGER / PUBLIC_CI_REQUIRED / GLOBAL_GOAL_ACTIVE`

## Public chain

1. Preregistration commit `02795524457d1dc9a8c3386dc421eeca18edab46` passed Lean Action
   run `30606350173`, build job `91079288544`.
2. Step-7 implementation commit `87b06e0c258b5fbc8f141a7242ce0ac8ae9ac4dc` passed run
   `30645129522`; immutable evidence `88c5e8f4552548de67a5d345f2fcb7e9f7f45a2e` passed run
   `30645443955`; checkpoint receipt `6cbe54fc16e32cab02e1e77da9620aead0f0992f` passed run
   `30645718046`.
3. Step-8 frozen implementation commit `6863823d119977a660d0643595cbfc61b7282018`
   passed Lean Action run `30653076645`, build job `91230777600`, in `2m18s`.
4. Docs-only immutable-evidence commit `0e22bd751a4e51c16fef3015fb1361b76f865df0`
   passed Lean Action run `30653415405`, build job `91231875566`, in `2m5s`.
5. The five frozen Lean blobs are identical between the step-8 implementation and evidence
   commits.

## Closed subnode

Once this closure ledger passes public CI, close only
`H12.speiser.levinson-montgomery-log-count-and-base-reduction`.

The unconditional compiled edge is:

```text
finite multiplicity-aware global count identity
-> one adaptive vertical preserving all strict-left divisor support
-> strict-left principal-log argument bounds on both vertical sides
-> actual top Jensen O(log(t+2)) and fixed-bottom control
-> finite bad-height stabilization
-> N_1^-(T) = N^-(T) + O(log T) for every sufficiently large real T.
```

The exact-count branch is compiled through every later contour step from one finite base. The
literal source-shaped base is `LevinsonMontgomeryHeightTenCertificate`; it propagates to a
strictly higher bottom without changing either actual multiplicity count.

## Open parent

Do not close `H12-LM-GLOBAL-INDENTED-COUNT-01`. Its first unavailable theorem is

```lean
theorem levinsonMontgomeryHeightTenCertificate_actual :
    LevinsonMontgomeryHeightTenCertificate
```

The open task is to certify the low-height sign and zero count offset, or to find a materially
different argument that fixes the invariant integer offset. The unconditional count dichotomy,
full Levinson--Montgomery Theorem 1 conjunction, Speiser equivalence, derivative-zero exclusion,
H12, and RH remain open.

## Classification

- `result=LEVINSON_MONTGOMERY_LOG_COUNT_FORMALIZED_AND_EXACT_BASE_ISOLATED`;
- `historical_route_coverage_delta=1`;
- `adaptive_uniform_negative_strip_delta=1`;
- `all_real_log_count_bound_delta=1`;
- `four_side_zero_winding_delta=1`;
- `height_ten_dependency_isolation_delta=1`;
- `levinson_montgomery_count_dichotomy_delta=0`;
- `speiser_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

## Rotation rule

After closure-ledger CI, stop only this local campaign and return to fresh cross-family
omission-seeking selection. The height-ten theorem remains a valid H12 re-entry candidate, but
adjacency alone gives it no priority. Historical routes are searched for omitted assumptions,
discarded branches, and later tools that may repair their exact failure points. Original
conjectures, falsification, and direct RH proof attempts remain open at every stage.

The persistent RH Goal remains active.
