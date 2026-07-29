# H1 Hardy--Littlewood Eta Remainder Attempts

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Status: `FULL_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_CI_PENDING`

## Fixed question

Can Lean prove Hardy--Littlewood Lemma 3's actual uniform eta remainder without an
`abs(s)` loss by isolating a finite bounded-variation mechanism in the consecutive
logarithmic phases, and then identify the ordered limit with
`(1-2^(1-s))*riemannZeta s` on `0<re(s)`?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `PARENT_CLOSURE` | H2 dyadic-dichotomy receipt `d85a370e4adaffdcf51e86fa8b38ff459518d491` passed run `30492021514`, job `90711944691`, in `1m38s`. | Stop only the local H2 finite-dichotomy campaign and rerank all historical families. |
| 2 | `USER_POLICY_ALIGNMENT` | Historical exploration is intended to find overlooked strength or missing combinations in human routes. Original conjectures and direct RH attempts remain open before historical exhaustion. | Rank source inferences by omission value, not by family novelty or adjacency. |
| 3 | `CROSS_FAMILY_SELECTION` | H10's actual curve step lacks a source-ready divisor stack; H12's next step couples three global count inputs; H2's next step is a full density argument. H1 Lemma 3 is one exact source statement with compiled consumers on both sides. | Select the actual eta remainder. |
| 4 | `PRIMARY_SOURCE_AUDIT` | Pages 284--286 show that Lemma 3 subtracts Lemma 2 at `x` and `x/2`, exactly canceling both principal terms. The source eta estimate has no independent `abs(s)` loss. | Reject crude adjacent-pair absolute values as the operative proof. |
| 5 | `OMISSION_CANDIDATE` | The actual phase ratio is near `-1`. Writing `u_n=(1-q_n)^(-1)*(u_n-u_(n+1))` converts the phase block to endpoints plus inverse-coefficient variation. Logarithmic increments are monotone and exponential chords are Lipschitz. | Preregister a direct finite phase proof rather than assuming the full source Lemma 2. |
| 6 | `PROJECT_INTERFACE` | `hardyLittlewoodEtaPartialSum` is literal, the eta-to-Theta Abel consumer compiles, and `hardyLittlewoodEta` is the actual zeta expression. Existence of an unnamed ordered limit would not connect these interfaces. | Make analytic identification a full-success requirement and a named partial boundary. |
| 7 | `PREREGISTRATION` | The fixed endpoint requires actual phase factorization, ratio, denominator separation, total variation, phase-block and eta-tail bounds, ordered convergence, zeta identification, critical-line specialization, and Theta composition. | Publish docs only and await public CI before editing `LeanLab/`. |
| 8 | `PUBLIC_GATE` | Docs-only preregistration commit `5402fc312747bf68a0bedcdd6e67b8dd71241ed2` passed Lean Action run `30492875305`, build job `90714768715`, in `1m53s`. | Open production editing at the fixed endpoint. |
| 9 | `FINITE_PHASE` | Lean proves the exact phase ratio, denominator norm at least one, inverse coefficient norm at most one, and total inverse-coefficient variation at most one. | Use finite inverse-difference summation on the actual source phases. |
| 10 | `PHASE_BLOCK` | `norm_hardyLittlewoodEtaUnitPhaseShiftedPrefix_le_four` proves every actual shifted unit-phase block is at most `4`, uniformly in block length when `1<=N` and `abs(t)<=N`. | Transfer the bound through decreasing power weights. |
| 11 | `ETA_BLOCK` | `norm_hardyLittlewoodEtaShiftedPrefix_le_four_mul_rpow` proves every finite actual eta block is at most `4*N^(-sigma)` for `sigma>0`, with no `abs(s)` loss. | Construct the canonical ordered limit and retain the same remainder constant. |
| 12 | `ORDERED_LIMIT` | The partial sums are Cauchy on `re(s)>0`; their `limUnder atTop` value converges locally uniformly and satisfies the literal ordered remainder. | Prove holomorphy and identify the value in the absolute-convergence half-plane. |
| 13 | `ZETA_IDENTIFICATION` | Odd/even splitting proves the ordered value equals `(1-2^(1-s))*riemannZeta s` for `re(s)>1`; the identity theorem extends equality to `re(s)>0`, `s!=1`. | Replace the canonical value by the project eta definition at the public remainder interface. |
| 14 | `SOURCE_SPECIALIZATION` | The actual project eta remainder and its critical-line specialization compile with constant `4` and source regime `abs(t)<=N`. | Discharge the existing Lemma 4 Abel-transfer premise. |
| 15 | `THETA_COMPOSITION` | `exists_hardyLittlewoodThetaValue_of_re_pos` composes the proved eta remainder with the existing Theta consumer and gives an explicit `8*(log 2)^-1*N^(-re(s))` tail. | Classify locally as full success; register Target/checks/axioms and run the full audit. |
| 16 | `LOCAL_AUDIT` | The 1181-line module and all registration files compile with warnings as errors; nine exact checks and nine axiom prints pass with only `propext`, `Classical.choice`, and `Quot.sound`; forbidden/resource scans and `git diff --check` are empty; full build passes `8805/8805`. | Freeze the implementation and publish the evidence chain before closing only this campaign. |
| 17 | `IMPLEMENTATION_PUBLIC_CI` | Frozen commit `e3341491b34959f2b1eb5d4e1fe2f6fc6cb6ac6f` passed Lean Action run `30495767931`, build job `90724079010`, in `2m17s`; the frozen five-file diff is empty. | Publish docs-only immutable evidence and require a second public CI. |

## Current frontier

- `compiled_left_context`: actual eta/zeta normalization and critical-line source definitions.
- `compiled_right_context`: exact eta-to-Theta Abel transfer and finite shifted mean square.
- `selected_edge`: proved actual uniform Lemma 3 eta remainder and zeta identification.
- `finite_result`: inverse-difference summation gives phase-block constant `4` and actual eta
  remainder constant `4`.
- `analytic_result`: the canonical ordered limit is locally uniform and holomorphic on
  `re(s)>0`, agrees with the project eta on `s!=1`, and feeds the existing Theta transfer.
- `strict_successor`: eta primitive-series identification in the moving source coordinate,
  eta-error second moment, source-X moment, and the Hardy--Littlewood parameter budget.
- `closed_obstacles`: `OBS-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01` and
  `OBS-H1-HARDY-LITTLEWOOD-ETA-SERIES-IDENTIFICATION-01`.
- `audit_state`: implementation public green; immutable-evidence CI, final-ledger CI, and
  closure-receipt CI remain.
- `not_claimed`: an eta-error moment, unconditional linear count, H1, or RH.
- `protected_files`: inherited modified and untracked files remain untouched and unstaged.
- `global_goal`: active.
