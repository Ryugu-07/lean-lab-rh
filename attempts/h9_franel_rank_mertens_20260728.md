# H9 Franel Rank--Mertens Correlation Attempt

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H9-FRANEL-RANK-MERTENS-01`

Node: `H9-FRANEL-RANK-MERTENS-QUADRATIC-01`

Mode: `LITERATURE`, with finite `FALSIFICATION` controls

Status: `MEANINGFUL_PARTIAL / IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_CI_PENDING`

## Fixed target

Reconstruct the source positive Farey ordering and one-based Franel discrepancy, specialize the
compiled arbitrary-test Farey transform to rank counts, prove the exact pointwise Mertens
remainder formula and its squared finite correlation expansion, and attempt the complete
Kanemitsu--Yoshimoto Theorem 3 gcd-kernel identity.

`FULL_SUCCESS` required the complete gcd-kernel formula. `MEANINGFUL_PARTIAL` required the actual
ordering and rank, exact pointwise and squared Mertens formulas, finite controls at
`N=0,1,2,3`, and the first unproved source correlation theorem in exact statement form.

## Attempt log

| phase | action | compiled result | decision |
| --- | --- | --- | --- |
| `SOURCE_ALIGNMENT` | Locked Franel 1924, Landau 1924, and Kanemitsu--Yoshimoto 1996. Matched `0<a<=q<=N`, excluding `0/1` and including `1/1`. | Theorem 3's sum convention exactly matches inherited `fareyPairs`. | Preserve the inherited pair set. |
| `ORDERING` | Sorted duplicate-free rational Farey values and connected `orderEmbOfFin` to lower-set cardinality. | Strict list, nodup, exact length, rank injectivity, `rank(get i)=i+1`, exact rank image. | Use one-based rational order only. |
| `COUNT_TRANSFORM` | Specialized the complex arbitrary-test transform to the lower-interval indicator and reflected it into `Rat`. | `rank(xi)=sum M(N/n)*completeCount(n,xi)` and `Phi=sum M(N/n)*n`. | Subtract before estimating. |
| `POINTWISE_REMAINDER` | Defined `n*xi-completeCount(n,xi)` and combined the transforms. | Exact normalized Mertens block-remainder discrepancy. | Square only after compilation. |
| `FINITE_QUADRATIC` | Squared and exchanged three finite sums. | `Phi(N)^2*fareySquaredDiscrepancy(N)=fareyMertensCorrelationQuadratic(N)`. | Enter the centered source proof. |
| `ENDPOINT_CONSTANT` | Applied the transform to the test supported at `x=1`. | `sum M(floor(N/n))=1`; hence `delta=(sum M*centeredRemainder+1/2)/Phi`. Centered remainder is `-1/2` at integer endpoints. | The source constant is derived, not guessed. |
| `SOURCE_LEMMA_7` | Applied the transform to a product of centered remainders. | Centered Farey correlation equals the Mertens-weighted modified Dedekind block; the double quadratic equals a triple Mertens/Dedekind sum. | Reduce to the three-term relation. |
| `THREE_TERM_ATTACK` | Transcribed Lemma 8 and searched Mathlib for Dedekind reciprocity. | No reusable theorem exists. The exact open proposition is `FareyDedekindThreeTerm`. Controls compile at `(1,1,1)`, `(1,2,3)`, `(2,2,2)`. | Stop at the preregistered meaningful-partial boundary. |
| `FRANEL_CONTROLS` | Computed actual Farey sets and both sides of Theorem 3 for `N=1,2,3`; retained `N=0` as no-division boundary. | `Phi=0,1,2,4`; squared discrepancy `=0,0,0,1/72`; positive gcd kernels `=1,1,5/3`; all positive final formulas compile. | Source transcription passes falsification. |
| `LOCAL_AUDIT` | Registered Target, checks, selected axiom prints; ran warning-as-error, scans, patch check, full build. | Standard axioms only; scans empty; full build `8780/8780`. | Freeze and require public CI. |
| `IMPLEMENTATION_PUBLIC_CI` | Pushed frozen implementation `e672420574994819213da3999e8c2e962e6c903c`. | Run `30372189487` attempt 1 failed before build because GitHub returned HTTP 500 while downloading Elan. Unchanged attempt 2 passed job `90319104548` in `2m29s`. | Keep the implementation frozen and publish docs-only immutable evidence. |

## Strongest compiled facts

- `fareyRankValue_get_ordered`
- `image_fareyRank`
- `fareyMertensWeight_sum`
- `fareyDiscrepancy_eq_mertens_remainder`
- `fareyDiscrepancy_eq_centered_mertens`
- `fareyPhi_sq_mul_squaredDiscrepancy_eq_correlation`
- `fareyCenteredCorrelation_eq_mertens_dedekind`
- `fareyMertensCenteredQuadratic_eq_dedekindTriple`
- `fareyFranelCorrelation_endpoint`

## Exact open obstacle

`FareyDedekindThreeTerm` states for positive `a,b,c`:

```text
s11(ab/c) + s11(bc/a) + s11(ca/b)
  = (1/12) * (
      gcd(a,b)^2*c/(a*b)
    + gcd(b,c)^2*a/(b*c)
    + gcd(c,a)^2*b/(c*a))
    + gcd(a,b,c)/2.
```

Here `s11` is the compiled centered block with `B1(integer)=-1/2`. This is a definition of the
open statement, not a theorem or certificate field. Re-entry should formalize the source's
three-variable residue classification and Bernoulli distribution relation, or find a direct
finite bijective proof. Numerical constant optimization is not the next step.

## Result boundary

- `result_class`: `MEANINGFUL_PARTIAL / FRANEL_MERTENS_CORRELATION_FORMALIZED`
- `historical_route_coverage_delta`: `1`
- `farey_order_rank_delta`: `1`
- `pointwise_mertens_delta`: `1`
- `finite_correlation_delta`: `1`
- `dedekind_three_term_delta`: `0`
- `franel_full_identity_delta`: `0`
- `hard_gap_delta`: `0`
- `rh_frontier_delta`: `0`

No Franel asymptotic estimate, Mertens growth estimate, H9, or RH is proved.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary after preregistration public CI; current
  governance, source conventions, worktree, preregistration, and inherited transform were
  rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
- `frozen_implementation`: `e672420574994819213da3999e8c2e962e6c903c`, public-green on
  run `30372189487`, attempt 2, job `90319104548`.
