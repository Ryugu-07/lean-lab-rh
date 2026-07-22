# H7 Finite-Prime Weil Ground-State Alignment Preregistration

Date: 2026-07-22

Campaign: `LITERATURE-20260722-H7-WEIL-GROUNDSTATE-ALIGN-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION_LOCAL / PUBLIC_CI_PENDING`

## Baseline and route decision

- `parent_commit`: `051ace38c80aebcde083432297c9fa01e02539e4`.
- `baseline_public_ci`: Lean Action run `29921844064`, build job `88929023824`, passed in
  `2m1s`.
- `previous_campaign`: the Historical Door Survey publicly selected the finite-prime Weil
  ground-state edge as the highest-value omission candidate within its source boundary.
- `dag_node`: `H7-WEIL-GROUNDSTATE-ALIGN-01`.
- `material_difference`: the prior atlas compared route endpoints. This campaign tests exact
  equality of the source and project objects before any spectral or convergence premise is used.
- `global_goal`: active; no result of this campaign is itself an RH proof.

## Corrected source frontier before proof edits

The source inventory already corrects one coarse statement in the atlas, but this correction is
not yet a project theorem or an alignment result:

- Connes 2026, Fact 6.4, proves that the Fourier transforms of the explicit prolate approximants
  `k_lambda` converge to Riemann `Xi` uniformly on closed substrips of `|Im z| < 1/2`, with the
  displayed line bound of order
  `lambda^(-1/2-alpha) / (1-2*alpha)`.
- Connes 2026 Section 6.6 and Connes--Consani--Moscovici 2025 identify the remaining limit bridge
  as comparison of the actual lowest eigenfunction `xi_lambda` with `k_lambda`, together with the
  simple-even ground-state condition.
- Groskin 2026, arXiv:2607.02828, claims an exact finite Guinand--Weil dictionary from each real
  even Galerkin vector to a compactly Fourier-supported test function. It is a July 2026 primary
  preprint and must be audited rather than assumed.

## Primary sources and pinned formulas

1. Connes--van Suijlekom, arXiv:2511.23257: distribution on `[0,L]`, symmetrized kernel,
   trigonometric basis, divided-difference matrix, and the simple isolated even ground-state
   real-zero theorem.
2. Connes--Consani--Moscovici, arXiv:2511.22755: `L=2*log lambda`, the isometry from
   `L^2([0,L])` to `L^2([lambda^-1,lambda],du/u)`, `QW_lambda`, its three explicit-formula blocks,
   the Galerkin spaces `E_N`, and the conditional rank-one spectral triple.
3. Connes 2026, arXiv:2602.04022, Sections 6.4--6.6: the explicit `k_lambda` approximation,
   proved `k_lambda` transform limit, and the two remaining steps.
4. Groskin 2026, arXiv:2607.02828, Lemmas 2.1--2.3 and Theorem 2.5: the finite coefficient-to-test
   dictionary, including diagonal derivatives, zero multiplicity, and the one-way scope warning.
5. Groskin 2026, arXiv:2605.20224: independent numerical implementation and normalization audit;
   navigation evidence only.

## Exact M0 inventory target

Create `research/h7_weil_groundstate_alignment_20260722.md` with one row for each item below.
Every row must be classified `EXACT`, `EXACT_AFTER_NAMED_CONJUGACY`, `SOURCE_ONLY`, `PROJECT_GAP`,
or `MISMATCH`, and must cite both the source formula and the project declaration when one exists.

1. `lambda > 1`, `L = 2*log lambda`, and prime cutoff `c = lambda^2 = exp L`; distinguish these
   from the project's contour-line parameter also named `c`.
2. `L^2([0,L],dx)`, `L^2([lambda^-1,lambda],du/u)`, and the project's smooth compact additive
   root class.
3. The Fourier bases `U_n`, `V_n`, even involution, finite spaces `E_N`, and coefficient
   normalization `u_0=v_0`, `u_{+/-k}=v_k/sqrt 2`.
4. The weighted centered root map
   `g(x)=exp(-x/2)*f(x+L/2)`.
5. Source additive star/convolution versus project `compactLaplaceConjInvolution` and
   `compactLaplaceAutocorrelation`.
6. Mellin/Fourier conventions and the exact map from a source Fourier--Mellin zero coordinate
   `z` to the project xi-zero parameter `s=1/2+i*z`.
7. The pole block `W_{0,2}`, including both endpoint moments; do not silently identify the full
   form with `compactWeilArithmeticQuadratic`, whose named definition omits the pole term after
   endpoint cancellation.
8. Prime powers `q=p^a <= exp L`, signs, factors `pi`, `Lambda(q)/sqrt q`, and support cutoff.
9. The archimedean digamma density, vertical-line normalization, and any remaining factor of
   `2*pi`.
10. The divisor/zero side, analytic multiplicity, reflection symmetrization, and absolute versus
    conditional convergence class.
11. The finite divided-difference matrix, including the derivative-valued diagonal.
12. The finite dictionary's direction: Galerkin vector to admissible test function, with no
    inverse or density claim.
13. Continuous form closure, lower-bounded selfadjoint operator, compact resolvent, and the exact
    simple/isolated/even hypotheses.
14. The three distinct limits: `N -> infinity` at fixed `lambda`, `k_lambda -> Xi`, and the still
    open `xi_lambda - k_lambda` comparison as `lambda -> infinity`.

## Proposed Lean bridge

Only after this preregistration passes public CI, introduce a narrowly scoped module if the API
audit confirms the statements are well-typed. The proposed checked spine is:

1. define the weighted centered additive root corresponding to a source function on `[0,L]`;
2. prove its project conjugate involution is exactly the weighted centered source star;
3. prove its project autocorrelation is `exp(-x/2)` times the source additive correlation;
4. prove the critical-line bilateral Laplace transform is the source Fourier--Mellin transform
   under `s=1/2+i*z`;
5. prove the endpoint transforms are exactly the two source pole moments;
6. if regularity permits without changing the source object, prove the resulting full arithmetic
   expression agrees term-by-term with the source form. Otherwise record the exact regularity or
   domain mismatch and do not manufacture a smooth substitute.

Final theorem names and exact Lean statements will be fixed in the alignment record before they
can become downstream premises. Every introduced declaration must receive exact TargetChecks and
selected axiom prints. No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or
resource relaxation is permitted.

## Success, falsification, and stopping criteria

- `success`: all fourteen M0 rows are adjudicated; every claimed equality is either a compiled
  Lean bridge or a verbatim source identity; the finite dictionary's actual contribution and the
  true open spectral/limit nodes are separated exactly.
- `meaningful_partial`: the weighted coordinate bridge compiles, but the full form equality is
  blocked by a precise source/project regularity or domain mismatch.
- `falsification`: the source finite form and the project form differ in sign, normalization,
  pole constraints, test class, or operator domain in a way not repaired by the named weighted
  conjugacy. Record `OBS-H7-WEIL-ALIGN-MISMATCH-01` and do not enter the spectral campaign.
- `no_progress`: the source data are insufficient to decide one or more rows; record the exact
  unresolved formulas and return to route selection.
- `local_stop`: stop when the M0 table and any admitted Lean bridge are publicly closed. This
  does not stop the persistent RH Goal.

## Assumption frontier and downstream decision

- `before`: the project has a compiled compact-smooth Weil positivity criterion, while the H7
  source uses an `L^2` form closure and finite trigonometric restrictions. Equality has not been
  established in Lean.
- `forbidden_inference`: numerical positivity, tiny eigenvalues, or matching zeros cannot prove
  simple-even structure, continuum form equality, or convergence.
- `if_exact`: register the corrected open child
  `H7-WEIL-GROUNDSTATE-APPROX-01` for the true eigenvector-to-`k_lambda` comparison and separately
  assess `H7-WEIL-GROUNDSTATE-SPECTRAL-01`.
- `if_mismatch`: register the mismatch obstruction and route-select without informal repair.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: no compaction in this campaign at preregistration.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

