# lean-lab — AI + Lean4 数学证明（3.0 方向 3）

> 冷启动必读。本文件由 Claude(arch) 维护，记录项目状态与决策；实现方为 GPT/codex。

## 目标
Mac（M4/24G）上搭 Lean4 + mathlib 环境，建立 AI 辅助证明工作流：**Lean4 编译器当幻觉闸门**——AI 定义问题范围 → 检索定理/文献/mathlib 已有成果 → 生成证明 → 编译打回即换思路。从本科/研究生难度起步，长期观察 agent 证明思路，积累 AI 辅助科研经验。

## 规格
见 `~/Downloads/spec_lean4_env_20260708.md`（实现前先读）。

## 当前状态
- 2026-07-08：GPT 已搭好 Lean4 + mathlib 环境。
  - `elan` 已安装；当前默认 Lean toolchain 为 `leanprover/lean4:v4.31.0`。
  - `/Users/karasuakamatsu/lean-lab` 已用 Lake `math` 模板初始化，依赖 mathlib `v4.31.0`。
  - 已执行 `lake exe cache get`，mathlib cache 显示 `No files to download` 且 `Already decompressed 8542 file(s)`。
  - 验收 hello proof：`LeanLab/HelloProof.lean` 中 `example : 2 + 2 = 4 := by norm_num` 已通过 `lake env lean LeanLab/HelloProof.lean`。
  - `lake build` 已通过（8561 jobs）。
  - attempts 日志已建立：`attempts/hello_proof.md`、`attempts/optional_tooling.md`。
  - 项目本地 Python venv：`.venv`，用于可选工具；已加入 `.gitignore`。

## 决策记录
- 环境装 Mac，后台稳定跑。
- LeanDojo 和 lean-mcp 类工具都试装，装不上不阻塞主线（命令行 `lake` 编译验证是底线能力）。
- 占位证明不算通过；每次尝试（成败+原因）记入 attempts log 供复盘。
- RH 是当前持续研究目标；允许直接攻击 RH 或任何开放中间命题。只有编译、公理审计、
  witness 和定义对齐后的结果才能成为证明资产。

## 常用命令
- 验证单文件：`lake env lean LeanLab/HelloProof.lean`
- 构建项目：`lake build`
- 缓存检查：`lake exe cache get`
- 启动 Lean LSP MCP：`.venv/bin/lean-lsp-mcp --lean-project-path /Users/karasuakamatsu/lean-lab`
- Python 工具环境：`.venv/bin/python`

## 可选工具状态
- LeanDojo：`.venv` 内已安装 `lean-dojo==4.20.0`，import smoke test 通过；但 trace smoke test 在 Lean 4.31.0 下失败，原因是 LeanDojo 的 `ExtractData.lean` 与当前 Lean 内部 API 不兼容。当前不作为主线工具。
- Lean LSP MCP：`.venv` 内已安装 `lean-lsp-mcp==0.28.0`，stdio MCP smoke test 通过；可列出 23 个工具，并能返回 diagnostics、run_code、goal state。

## 下一步
- 完成 3 个本科级定理的 AI 辅助形式化。
- 每个定理都要有 attempts 日志：statement、策略、编译结果、失败原因/换路记录、token 花费（若可得）。
- 证明文件中不允许残留占位证明。

## RH current handoff (2026-07-17, V4.1 governance active)

> RH 是你的目标。你可以直接攻击它，也可以攻击通往它的任何未决命题。你的每一次尝试——成功编译的定理、失败后记录的障碍——都是这个项目的正资产。唯一的规则是：让编译器替你说话。

- The canonical authority is `research/rh_governance_current.md`; V4.1 is preserved verbatim in
  `research/rh_directive_v4_1_20260717.md`.
- The global Goal remains active. `LITERATURE`, `DISCOVERY`, `PROOF-ATTEMPT`, and `FALSIFICATION`
  are the four operating modes. RH, W2/G7, and M2/G3 are open and require no preapproval.
- All numerical quotas, proof freezes, and former input-side review gates are abolished. Local
  `STOP` or `NO_PROGRESS` enters `ROUTE_SELECTION` and never pauses the global Goal.
- Exposure remains the first priority in parallel. P1b is complete: clean-context Sol 5.6 max
  found no P0-P2 issue and two P3 precision corrections; see
  `research/li_weil_sol_max_review_20260717.md`.
- P2 remains pending because public GitHub/Zulip prose must be human-authored under current
  mathlib policy. This affects external wording only, not proof work.
- Every direct attack preregisters its exact statement, success/falsification criteria, and known
  obstacle in `attempts/`; failure becomes an OBS node. No unproved statement becomes a premise.
- Loop 8 is publicly closed at exact Polymath equation `(39)`. Implementation
  `af6c80c42c0abdfb1cf91147e74a8b88263b20ea`, evidence
  `7cf65e6d19afb963e9bb910a1a0e763a5f234344`, and closure
  `1aaf485969961d73ffb480870380f613afb2165c` passed their recorded public CI runs.
- Loop 9 of `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01` has compiled both actual
  source contour shifts `(rtn-def)` and `(RTN-def)` for arbitrary complex shifts on the strict
  same-half-plane domain. The implementation commit
  `74946858f75e27b306cbf43042df74c447b18740` passed public CI run `29654348324`, build job
  `88105922988`, in `2m16s`; evidence commit
  `03ccacba97674a8adabf5e2f5b9b6f810539000e` passed run `29654669529`, build job
  `88106762342`, in `1m35s`. The next exact source gate is the effective term/remainder estimate
  pair in Propositions 6.1 and 6.3; numerical certificates, H6-E/G8, and RH remain open.
- Loop 10 is preregistered as a `PROOF-ATTEMPT` on the exact Proposition 6.1 effective estimate
  for every positive heat residue `r_(t,n)(sigma+iT)`, with `T>10` and `0<t<=1/2`. Its first
  source-faithful obstacle is Lemma 5.1(v), the explicit complex Stirling remainder; Proposition
  6.3 is deferred because it additionally depends on the absent Arias de Reyna `C_k`/`RS_K`
  expansion. No Loop 10 proof source may be edited before public preregistration CI is green.
- Pending publication-policy ruling, local AI-authored `README.md`, `CONTRIBUTIONS.md`,
  `VERIFYING.md`, and related exposure drafts remain uncommitted and must not enter a proof or
  preregistration commit.
- Current route selection corrected the H6 literature frontier: Platt--Trudgian, arXiv
  `2004.09765`, Corollary 2 already proves `Lambda<=0.2`. The former H6-Q description as an open
  improvement from `0.22` is superseded.
- Latest publicly closed campaign is `CAMPAIGN-20260717-H6-GENERAL-STRIP-CONTRACTION-01`
  (`LITERATURE`). It proves arbitrary-base squared-strip contraction and the exact `t+y^2/2`
  all-real endpoint, exposing the last de Bruijn step after a Polymath canopy certificate.
  Preregistration `2685003e8f6617add0701a2b1680328ca8c4943f`, implementation
  `9ddee42657933ccd94533affa25f83a75392a1ea`, and evidence
  `307b5e29ed65b909e8efffb126787b9176c93453` passed public CI runs `29571892273`,
  `29572752471`, and `29572973709`.
- Campaign `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01` is publicly closed as
  `KNOWN_THEOREM_FORMALIZED`. Lean proves compact-uniform Hermite
  scaling, repeated-zero backward upper escape, the complete conditional three-region criterion,
  its exact `t0+y0^2/2` all-real consequence, and the Table 1 second-row corollary at `1/5`.
  The three region certificates themselves, unconditional `Lambda<=0.2`, H6-E/G8, and RH remain
  open; none is imported as a hidden premise.
- Fresh route selection chooses
  `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`. Its fixed endpoint is all three
  specialized second-row certificates and the hypothesis-free theorem
  `deBruijnNewmanAllZerosReal (1/5)`. Loop 1 first compiles the exact finite-height-RH to
  initial-region transport; this is not permission to assume the Platt--Trudgian computation.
- The external Polymath computation repository was inspected at commit
  `5fde84e11ba80adad5c225a4eaa0a28b68dc925d`. It contains the exact row's Arb output but grants no
  usable software license. No code or decimal result is imported, and every certificate must be
  independently checked by Lean.
- Preregistration commit `652c816cca25c6517fee9654511335ce912ac132` passed public Lean Action CI
  run `29629630395`, build job `88040634155`, in `2m16s` before proof-source edits began.
- Loop 1 now compiles `riemannHypothesisUpTo`, its consequence from full RH, the general
  finite-height-RH-to-initial-region bridge, and the exact second-row specialization through
  `3*10^12`. The `x=0` boundary is discharged independently by imaginary-axis nonvanishing; the
  positive branch uses the exact `x/2` ordinate. The standalone checks, four exact witnesses,
  three standard-only axiom prints, forbidden scans, and the full 8,704-job build pass locally.
- This is a conditional checkpoint only: the finite RH computation is not asserted, all three
  unconditional Table 1 certificates and the no-hypothesis `1/5` endpoint remain open, and
  implementation commit `ac96523034b36e2bfafdb007d6dcd95d8e89b625` passed public Lean Action CI
  run `29630082237`, build job `88041893271`, in `1m52s`. Evidence commit
  `0cd4c215d59c4e37949c09160ad65789bd1fe61d` passed run `29630173782`, build job `88042132339`, in
  `1m49s`. Loop 1 is publicly checked. Loop 2 attacks the source-normalized effective
  Riemann--Siegel approximation and error consumer used by the final and barrier certificates.
- Loop 2 is now exactly preregistered around Polymath Theorem 1.3 and Corollary 1.4: define every
  source normalization quantity, prove the `log M_0` derivative and `B_t` nonvanishing, and compile
  the strict approximation-error test through the exact second-row final-region predicate. It is
  not satisfied by an abstract norm lemma or by interval infrastructure detached from `H_t/B_t`.
  Preregistration commit `be2167f3dda7f7b43aec34a1ac0acce270df7337` passed public CI run
  `29630529731`, job `88043072197`, in `1m53s` before proof-source edits.
- Loop 2 is locally complete as source infrastructure. Lean now has every displayed normalization
  and upper-error expression, the lower-half-plane branch identities, `B_t` nonvanishing, exact
  second-row parameter-region inclusion, and the explicit final-region certificate consumer.
  Source-definition checks, seven theorem witnesses, seven standard-only axiom prints, forbidden
  scans, and the full 8,705-job build pass locally. Implementation commit
  `3339ea0f0d6b44f656afd99c388ad313f6b18ed1` passed public CI run `29631298328`, job
  `88045278213`, in `1m57s`. Evidence commit `ba361a944fca85ecafde771761c03f3c0e6f3e05`
  passed run `29631407988`, job `88045594759`, in `2m11s`. Loop 2 is publicly checked.
- The effective approximation proposition and strict finite-sum inequalities are not proved, so no
  unconditional final region or `Lambda<=1/5` is claimed. Loop 3 attacks the paper's imaginary
  Gaussian heat-kernel identity and xi-coordinate form; the existing real-shift theorem moves
  heat time backward and does not cover this edge. The campaign and persistent RH Goal stay active.
- Loop 3 is now preregistered around Polymath equation `(htz)`. Its fixed outputs are the general
  variance-two imaginary-shift identity from time `t` to `t+r^2`, the `r=sqrt(t)` reconstruction
  from `H_0`, and the exact xi-coordinate integrand after `Y=2v`. Product integrability and Fubini
  are mandatory; a pointwise Gaussian MGF or a theorem assuming the missing premise is rejected.
  Preregistration commit `38dfa81b2918bf86495954f487cb11a71a89895e` passed public CI run
  `29631894291`, build job `88047126110`, in `1m50s`, before proof-source edits.
- Loop 3 is locally complete as `KNOWN_THEOREM_FORMALIZED`. Lean proves the exact complex MGF,
  absolute-exponential Gaussian majorant, imaginary cosine multiplier, full product integrability,
  general `t -> t+r^2` identity, `H_0` specialization, and exact `(htz)` xi form. Five statement
  witnesses, five standard-only axiom prints, forbidden scans, and the full 8,706-job build pass.
  This has `hard_gap_delta=0`: Titchmarsh `(xio)`, the `R_(0,N)` contour/residue decomposition,
  effective approximation, numerical regions, `Lambda<=1/5`, H6-E/G8, and RH remain open. Public
  Implementation commit `0601c75a42e0f5218541ef5833f9687fb850c5f2` passed public CI run
  `29632643337`, build job `88049238613`, in `2m18s`. Evidence commit
  `c6754490e2037a4d867dedee9878943bdad87016` passed run `29632785404`, build job
  `88049632427`, in `1m43s`. Loop 3 is publicly checked; the campaign and persistent RH Goal
  remain active. Loop 4's next exact gate is the fixed `5*pi/4` infinite contour and its finite
  residue shift, not an assumed contour interface.
- Loop 4 is preregistered in
  `research/h6_polymath_table_row_certificates_prereg_20260718.md`, with proof-source edits gated
  on public CI. It fixes `L_N(v)=N+1/2+exp(5*pi*i/4)*v`, the principal-power source kernel, absolute
  integrability, explicit pole subtraction, vanishing end segments, the finite shift
  `R_(0,0)=sum_(1..N) r_(0,n)+R_(0,N)`, and Titchmarsh/Polymath `(xio)` itself. The newly audited
  Mathlib route is the Poincare smooth-homotopy curve-integral theorem, which handles the
  non-orthogonal affine parallelogram after removable extension. A proper compiled prefix must be
  logged as infrastructure and does not close Loop 4 or support an RH progress claim.
- Loop 4 preregistration commit `80ac70759296e9823a5b55f4ec12afda109364b5` passed public CI run
  `29633356952`, build job `88051178220`, in `1m51s`. The attempted full contour/`(xio)` edge is
  locally `PARTIAL / BLOCKER_EXPOSED`. `DeBruijnNewmanPolymathRiemannSiegelContour.lean` compiles
  the fixed source-line geometry, principal-branch safety, denominator lower bound, exact Gaussian
  majorant, absolute integrability, and every positive-integer residue limit
  `n^(-s)/(2*pi*i)`. Five exact witnesses, five standard-only axiom prints, forbidden scans, and
  the full 8,707-job build pass locally. The first unclosed dependency is the derivative-compatible
  removable extension of the pole-subtracted kernel on one affine strip, followed by the finite
  Poincare parallelogram identity and vanishing end segments. The finite residue shift and
  Titchmarsh `(xio)` remain open. Implementation commit
  `7bb3101bc9ecc4698416ec6bfa5d296494a07a46` passed public CI run `29634900588`, build job
  `88055411542`, in `1m51s`. Evidence commit `0fcfbd510180161f82cd3ee2cc7b5f0e17c45fe0`
  passed run `29635011657`, build job `88055710345`, in `1m52s`. Loop 4 is publicly checked as a
  proper prefix; the campaign and persistent RH Goal remain active.
- Loop 5 is preregistered at Loop 4's first uncancelled dependency. Its fixed endpoint is
  `I_N(s)=(N+1)^(-s)+I_(N+1)(s)` for the actual source integrals. It requires a derivative-compatible
  removable single-pole subtraction, the finite nonorthogonal Poincare parallelogram with explicit
  orientations, and vanishing of both truncation end segments. An assumed residue theorem,
  abstract remainder, local residue alone, or finite identity without the infinite tail limit is
  rejected. Preregistration commit `25f6f43132acec6c3fc066cd800933b0f877455e` passed public CI
  run `29635161693`, build job `88056094834`, in `2m15s`; Loop 5 proof-source edits are now
  admitted.
- Loop 5 now compiles its exact infinite endpoint locally:
  `deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift` proves
  `I_N(s)=(N+1)^(-s)+I_(N+1)(s)`. The proof constructs a `dslope`-based holomorphic removable
  remainder, evaluates the finite one-pole boundary, proves both short ends vanish under a pure
  Gaussian majorant, and passes both long sides to full-line integrals. The finite proof uses a
  pullback rectangle with upper-parameter stagger `sqrt(2)/2`, rather than the literal symmetric
  finite parallelogram in preregistration; the stagger disappears in the exact infinite limit and
  the deviation is logged in the attempt file. Targets, five exact witnesses, and five selected
  axiom prints pass; the selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
  Forbidden scans, `git diff --check`, and the full 8,708-job build pass locally.
  This is `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`, `route_infrastructure_delta=1`. Next prove
  the finite induction/prefactor decomposition, then attack Titchmarsh `(xio)`. The campaign and
  persistent RH Goal remain active. Implementation commit
  `580bc73436b1571bb6096d2c85071562481598d0` passed public CI run `29637266988`, build job
  `88061673433`, in `2m2s`.
- Loop 5 evidence commit `0c2d932ce88b723f69ffe90d70b4e54c70d0056f` passed public CI run
  `29637397940`, build job `88062010108`, in `2m3s`.
- Loop 6 is preregistered at the first remaining source dependency. Its fixed endpoints are
  `I_0(s)=sum_(k<N)(k+1)^(-s)+I_N(s)` and the exact prefactor transport
  `R_(0,0)(s)=sum_(k<N)r_(0,k+1)(s)+R_(0,N)(s)`. It must induct from the public adjacent shift,
  preserve the source `Finset.range` indexing, and distribute the compiled exact prefactor. An
  assumed finite identity, detached telescoping lemma, or raw identity without prefactor transport
  is rejected. Proof-source edits are gated on public preregistration CI. If successful, the next
  attack is the Titchmarsh `(2.10.1)--(2.10.6)` recurrence/analytic-continuation chain for `(xio)`;
  the campaign and persistent RH Goal remain active.
- Loop 6 preregistration commit `0e6ce9b44f72d81ddad115e2a953198bd43c50fd` passed public CI run
  `29637526635`, build job `88062338513`, in `1m32s`. The fixed endpoint now compiles locally:
  `deBruijnNewmanRiemannSiegelRawIntegral_finite_shift` proves the exact finite `I_0`
  decomposition, and `deBruijnNewmanRiemannSiegelR0N_finite_decomposition` transports it through
  the exact source prefactor. Both exact witnesses and selected axiom prints pass; the selected
  axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Forbidden scans,
  `git diff --check`, and the full 8,709-job build pass. This is `KNOWN_THEOREM_FORMALIZED`,
  `hard_gap_delta=0`, `route_infrastructure_delta=1`. The next exact gate is the Titchmarsh
  `(2.10.1)--(2.10.6)` recurrence/analytic-continuation chain for `(xio)`; effective approximation,
  numerical certificates, H6-E/G8, and RH remain open. The campaign and persistent RH Goal remain
  active. Implementation commit `7ea4238b1f1159d5e59850406fa5b8d3bbebbca4` passed public CI run
  `29637745080`, build job `88062926702`, in `1m51s`.
- Loop 7 is preregistered as a `PROOF-ATTEMPT` on the complete source equation `(xio)`:
  `(1/8)*riemannXi(s)=R_(0,0)(s)+R_(0,0)^*(1-s)` for every noninteger `s`. The fixed mandatory
  spine is Titchmarsh `(2.10.1)--(2.10.6)`: actual `Phi(a)` contour integrability, translation and
  one-residue recurrences, elimination and specialization, slanted-ray Mellin/Fubini on
  `1<re(s)`, analytic dependence, and continuation. An abstract recurrence, assumed contour
  identity, half-plane-only theorem, or `(xio)` premise is rejected. A compiled proper prefix is
  logged as `PARTIAL / BLOCKER_EXPOSED`, not success. Proof-source edits are gated on public
  preregistration CI; the H6-Q1 campaign and persistent RH Goal remain active.
- Campaign `CAMPAIGN-20260717-H6-THRESHOLD-CLOSEDNESS-01` (`LITERATURE`) proves the exact
  endpoint `IsClosed {t : R | deBruijnNewmanAllZerosReal t}`. Route selection rejects weakening
  to simple zeros or compact-uniform hypotheses. The proof combines joint continuity,
  nonvanishing of each spatial entire function, isolated zeros, and Jensen's zero-free logarithmic
  circle mean. Preregistration commit `02758ff243c3f8cd434eb3c007a2a5f6b094fea7` passed public
  CI run `29515723482`, job `87680126242`, in `1m56s`, before proof-source edits began.
- This campaign can close only H6-H2 threshold closedness. De Bruijn forward preservation,
  nonempty upper-time existence, H6-E/G8, W2/G7, M2/G3, and RH remain open.
- Local implementation now compiles the exact endpoint
  `isClosed_setOf_deBruijnNewmanAllZerosReal`. The new module proves `Phi>0`, `H_t(0)!=0`, joint
  time-space continuity, full-multiplicity Jensen zero persistence, and a nonreal isolating ball.
  Targets, four exact TargetChecks, and four standard-only axiom prints pass in an 8,684-job build.
  Classification is `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`,
  `route_infrastructure_delta=1`. Forbidden proof-token, declaration, and resource-relaxation
  scans are empty, `git diff --check` passes, and the full 8,688-job build succeeds; public
  implementation commit `6322bbd59d25f919befc91cd5a057251bcf94cb4` passed Lean Action CI run
  `29518062294`, build job `87687972172`, in `2m7s`. Evidence-backfill commit
  `c5b9405befd3029f04b1301f55a8a9c45074dce4` passed run `29518417233`, build job `87689151089`,
  in `1m36s`; the campaign is publicly closed and the persistent RH Goal returns to fresh
  value-ranked route selection after closure CI.
- Current local closure checks pass: exact module, Targets, four exact TargetChecks, four
  standard-only axiom prints, forbidden scans, `git diff --check`, and the full 8,688-job build.
- Closure commit `7fc9fb62c308f3a97ff11689a273d23fba62d113` passed public Lean Action CI run
  `29518879967`, build job `87690702434`, in `1m37s`.
- Fresh value-ranked selection chooses
  `CAMPAIGN-20260717-H6-FORWARD-PRESERVATION-01` (`LITERATURE`). Its indivisible endpoint is
  `t<=tau -> deBruijnNewmanAllZerosReal t -> deBruijnNewmanAllZerosReal tau` for arbitrary real
  times, multiplicities, and infinite zero sets. Simple-zero, finite-degree, bounded-time, and
  spacing weakenings are rejected.
- The fixed attack reconstructs de Bruijn's universal-factor mechanism through source order-one
  growth, the vendored genus-one Hadamard factorization, vertical-shift averaging, iterated `cosh`
  multipliers converging to the exact heat multiplier, and Jensen zero persistence. Mathlib has
  no packaged Laguerre-Polya, real-rootedness preserver, or Hurwitz theorem. Preregistration
  commit `6e10d6eb74f038575e1d6ab4dcde92eb4e58b2ce` passed public Lean Action CI run
  `29520281656`, build job `87695371156`, in `1m51s`.
- The exact endpoint `deBruijnNewmanAllZerosReal_mono` now compiles locally in
  `DeBruijnNewmanForward.lean`. The proof establishes source order one, eliminates the linear
  Hadamard exponent, proves strict canonical-product comparison for vertical shifts, iterates the
  resulting all-real-zero averages, identifies the scaled `cosh` multiplier limit with the exact
  forward heat integral, and uses Jensen persistence to exclude a nonreal limit zero.
- Targets, the exact TargetCheck, and four axiom prints pass; every selected theorem has exactly
  `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. The new module is
  diagnostic-free under default limits, all forbidden scans are empty, `git diff --check` passes,
  and the full 8,689-job build succeeds. Implementation commit
  `344b4669224a5beb9e7c9a99a176b24735688986` passed public Lean Action CI run `29526887492`,
  build job `87717424885`, in `2m47s`. Evidence-backfill commit
  `b6e9dd7f6492f60574be68796f38818661422359` passed run `29527202922`, build job `87718477219`,
  in `1m57s`. H6-H2c is publicly closed as `KNOWN_THEOREM_FORMALIZED`, with
  `hard_gap_delta=0` and `route_infrastructure_delta=1`. Return to fresh value-ranked route
  selection; threshold nonemptiness/upper-time existence, H6-E/G8, W2/G7, M2/G3, and RH remain
  open, and the persistent RH Goal remains active.
- Fresh value-ranked route selection chooses `CAMPAIGN-20260717-H6-UPPER-HALF-01`
  (`LITERATURE`). Its indivisible endpoint is the quantitative de Bruijn contraction
  `0<=t<=1/2 -> H_t(z)=0 -> Im(z)^2<=1-2*t`, together with the unconditional conclusion that all
  zeros of `H_(1/2)` are real. Polynomial-only, epsilon-width, conditional, and simple-zero
  weakenings are rejected.
- The new proof angle pairs conjugate genus-one Weierstrass factors, constructs conjugation on the
  multiplicity-bearing divisor index, subtracts `a^2` from squared strip width at every vertical
  average, and then reuses the compiled finite `cosh` iteration and Jensen limit persistence.
  Exact preregistration is in `research/h6_upper_half_prereg_20260717.md`. Preregistration commit
  `502864b4a84740600c80a4864f3a3e3deb331c46` passed public Lean Action CI run `29528426983`,
  build job `87722558836`, in `1m50s`; fixed-architecture implementation is active.
- H6-H2d is locally complete in `DeBruijnNewmanUpperHalf.lean`. Lean proves the exact quantitative
  endpoint `0<=t<=1/2 -> H_t(z)=0 -> Im(z)^2<=1-2*t` and the unconditional witness
  `deBruijnNewmanAllZerosReal (1/2)`. The proof preserves analytic multiplicity under conjugation,
  pairs genus-one factors over a divisor involution, proves one-step squared-strip contraction,
  iterates it for every positive finite `cosh` approximant, and transfers the closed strip through
  an isolating-ball Jensen argument.
- The exact module, Targets, both endpoint TargetChecks, and eight selected axiom prints pass. All
  selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`; placeholder,
  declaration, native-decision, resource-relaxation scans and `git diff --check` are clean; the
  full 8,690-job build succeeds. Classification is `KNOWN_THEOREM_FORMALIZED`, with
  `hard_gap_delta=0` and `route_infrastructure_delta=1`. This closes threshold nonemptiness and
  proves the classical bound `Lambda<=1/2`; H6-E/G8 (`Lambda<=0`), W2/G7, M2/G3, and RH remain
  open. Implementation commit `8669c2db7577eaa718684e9e9ec052062b5488fa` passed public Lean Action
  CI run `29531232787`, build job `87731748374`, in `2m6s`. Evidence-backfill commit
  `ac128f4db100fdac0d47c670e0dcbd832ddb6005` passed run `29531495280`, build job `87732612433`,
  in `1m47s`. H6-H2d is publicly closed as `KNOWN_THEOREM_FORMALIZED`; the persistent RH Goal
  remains active and returns to fresh value-ranked route selection after closure CI.
- Governance commit `5c0a3eec14afbd02767e6b67fd4f7ba5c183a782` is public; Lean Action CI run
  `29491764123`, build job `87599314511`, passed in `2m10s`.
- The later supplied `RH_GOVERNANCE_V4_PATCH.zip` contributes the Sol H0-H14 historical census,
  progress audit, literature registry, Batch A instruction, and V4 source. They are imported into
  `research/` with V4.1 precedence: H1/H2/H6 route cards remain first-priority work, while old
  freezes, cooldowns, and numerical allocations have no force.
- Active direct campaign `PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01` targets the exact RH-equivalent
  statement `deBruijnNewmanAllZerosReal 0`. Its preregistration commit
  `4405d60c2a33444f8ae43f2406631cc80faff356` passed public CI run `29532612360`, build job
  `87736257748`, before proof-source edits.
- Implementation loop 1 is locally complete. `DeBruijnNewmanDynamics.lean` proves absolute
  summability of the multiplicity-aware regularized divisor force, the simple-zero ratio
  `H_t''/(2*H_t')=force`, a strict joint real Frechet derivative, and the exact path law
  `x'(t)=2*force`. Targets, five exact TargetChecks, five standard-only axiom prints, forbidden
  scans, `git diff --check`, and the 8,691-job full build pass.
- This first spine is known source infrastructure only: `hard_gap_delta=0`,
  `route_infrastructure_delta=1`. Implementation commit
  `ce65db1c0379a4accfef579c9e8c08995662dc19` passed public Lean Action CI run `29534356022`,
  build job `87741989620`, in `2m36s`; the first spine is public.
- Implementation loop 2 is publicly complete. Product-domain IFT plus conjugation uniqueness gives
  locally unique real simple-zero paths and local pair ordering. Removing both complete simple-zero
  fibers gives an absolutely convergent `pairRemainder` and Lean proves
  `force(t,s)-force(t,r)=2/(s-r)+pairRemainder`, hence
  `(gap^2)'=8+4*gap*Re(pairRemainder)` for real anchored paths.
- The loop-2 module, exact Targets, eleven campaign TargetChecks, twelve standard-only campaign
  axiom prints, empty forbidden scans, `git diff --check`, and the 8,691-job full build pass.
  Classification remains route infrastructure with `hard_gap_delta=0` and campaign-level
  `route_infrastructure_delta=1`. Implementation commit
  `03ce2ac2ee68b7d9a6d48d56aed37ab40836c30d` passed public Lean Action CI run `29536815968`,
  build job `87750004173`, in `1m54s`.
- The campaign stays active. Next is a theta-specific, height-aware integrated estimate on the
  pair-removed remainder and global continuation up to the first possible repeated zero. A fixed
  positive height-uniform gap is not used. H6-E/G8 and RH remain open.
- Loop 3 has now tested the generic adjacent-pair sign mechanism. Lean proves every remaining
  term has nonpositive real part, hence `(gap^2)'<=8`, and integrates it to
  `gap(a)^2>=gap(b)^2-8*(b-a)`. A middle zero contributes positively, so adjacency is necessary.
- `H6GapVelocityAudit.lean` proves the bound is generically sharp: an exact quadratic backward-heat
  pair with terminal gap `epsilon` collides after `epsilon^2/8`, and such a collision lies inside
  every proposed positive uniform interval.
- Record local obstruction `OBS-H6-ADJACENT-GAP-EIGHT-01`. This closes only the generic
  adjacent-gap branch with `hard_gap_delta=0`; theta-specific continuation, the first repeated
  zero, H6-E/G8, and RH remain open. The exact modules, Targets, seven new TargetChecks, seven
  selected standard-only axiom prints, empty forbidden scans, `git diff --check`, and the full
  8,692-job build pass. Implementation commit `ce5b0c405f06078f549c6a27a477df04ccbcfb35`
  passed public Lean Action CI run `29538670221`, build job `87755892757`, in `1m58s`; the global
  Goal remains active and returns to route selection after this campaign gate.
- Fresh route selection chooses `DISCOVERY-20260717-H6-HEAT-LI-MOMENTS-01`. This is materially
  different from the failed generic gap and reverse-Li branches: it uses the exact positive
  theta-kernel cosh transform after the coordinate `z=-i*(2*s-1)`.
- The fixed endpoint is all-real-time positivity of the first two source heat-Xi Li quantities,
  with exact moment factors `F(1)=8*A`, `F'(1)=16*B`, `F''(1)=32*C` and a kernel-checked
  `B^2<=A*C` witness. This is finite route infrastructure with `hard_gap_delta=0`; all-index
  positivity at time zero remains RH-equivalent and is not inferred.
- Exact preregistration is in `research/h6_heat_li_moments_prereg_20260717.md`. No Lean proof
  source is edited until its public CI passes. The persistent RH Goal remains active.
- The preregistration gate passed: commit `05b2b57e392ab53c0aeb9488cd7e31d28f9ff8f0`, public Lean
  Action CI run `29539585856`, build job `87758769100`.
- `DeBruijnNewmanLiMoments.lean` is locally complete. It proves, for every real `t`, the exact
  reflection `F_t(1-s)=F_t(s)`, identity `F_0=riemannXi`, heat equation
  `partial_t F=(1/4)*partial_s^2 F`, factors `F_t(1)=8A`, `F_t'(1)=16B`, `F_t''(1)=32C`, both first-two Li formulas, the positive
  weighted inequality `B^2<=A*C`, zero imaginary parts, and strict real positivity. The bundled
  endpoint is `deBruijnNewmanHeat_firstTwoLi_endpoint`.
- The Cauchy-Schwarz certificate is source-specific: with
  `W=exp(t*u^2)*Phi(u)*cosh(u)` and `X=u*tanh(u)`, Lean expands the nonnegative integral
  `integral W*(A*X-B)^2` and combines it with `integral W*X^2<=C`. No generic backward Li
  transfer is reused.
- Standalone compilation, Targets, the complete exact TargetCheck, seven selected standard-only
  axiom prints, forbidden declaration/proof/resource scans, and `git diff --check` pass; the full
  build succeeds with 8,693 jobs. Classification is `DISCOVERY_FORMALIZED`,
  `hard_gap_delta=0`, `route_infrastructure_delta=1`. Implementation commit
  `2bc304e9fe2473519c398269b26b0b06b715e593` passed public Lean Action CI run `29541314279`, build
  job `87763968249`, in `2m19s`. Evidence-backfill commit
  `1a7d3d6d8ef08e7726aeb8dff261372822d49b6e` passed run `29541519607`, build job `87764575644`,
  in `2m07s`. The campaign is publicly closed; the finite endpoint is not extrapolated to the
  all-index RH-equivalent criterion. The persistent RH Goal returns to value-ranked route selection.
- Fresh selection opens `AUDIT-20260717-H6-POSITIVE-COSH-LI3-01` (`FALSIFICATION`). It fixes a
  positive two-atom `cosh` transform at `log 2` and `10*log 2`, normalized with masses `1/8` and
  `7/8` at `s=1`. Lean must verify entire-ness, reflection, positive coefficients, the exact
  standard first-three Li expressions, positive first-two signs, and a strictly negative third
  sign using Mathlib's certified interval for `log 2`.
- Success records `OBS-H6-POSITIVE-COSH-LI3-01`: generic positive-kernel and Hankel moment
  structure cannot scale H6-Z to all indices. This says nothing about the actual theta kernel;
  H6-E/G8, W2/G7, M2/G3, and RH remain open. No proof-source edit is allowed before public
  preregistration CI passes.
- Preregistration commit `316ece356aaf5a11f2ddd18ff91da7a9f2ac73e3` passed public Lean Action CI
  run `29542262029`, build job `87766756340`, in `1m56s`. The 501-line
  `H6PositiveCoshLiAudit.lean` module now compiles the fixed model and its exact first-three Li
  formulas with strict signs `(+,+,-)`. The negative third sign is certified from exact
  hyperbolic values and Mathlib's rational bound for `log 2`.
- Exact Targets/TargetChecks, five standard-only axiom prints, empty forbidden scans,
  `git diff --check`, and the 8,694-job full build pass. Local classification is
  `BRANCH_FALSIFIED`, `hard_gap_delta=0`. Immutable implementation commit
  `5fdfc5c7437349735c57552a75838f16b4d63f5e` passed public Lean Action CI run `29543145545`, build
  job `87769424525`, in `1m55s`. Evidence-backfill commit
  `61ce528793a9fc04e4a6b26ba83463cf0557bafc` passed run `29543336971`, build job `87770059112`,
  in `2m06s`. The campaign is publicly closed; the persistent RH Goal returns to value-ranked
  route selection.
- Fresh selection opens `DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01`. It must extend the exact
  theta moments by `D`, prove ordered covariance `B*C<=A*D`, derive the standard third heat-Li
  formula, identify time zero with `liCoefficientCandidate 2`, and compile its strict positive
  real sign. The new mechanism combines covariance with the existing exact time-zero bound
  `liCoefficientCandidate 0<1`; it is not the generic positivity claim just falsified.
- The finite endpoint is below RH and has expected `hard_gap_delta=0`. Numerical quadrature only
  selected the target. No Lean proof source may be edited before the preregistration commit passes
  public Lean Action CI.
- The preregistration gate passed: commit `6c1c8c0defb2186ef20701ae9e33ca6be95c4daa`, public Lean
  Action CI run `29544246770`, build job `87772850526`, in `1m45s`, before proof-source edits.
- `DeBruijnNewmanThirdLi.lean` is locally complete. It proves fourth-moment integrability and
  positivity, `F_t'''(1)=64*D_t`, the exact ordered covariance `B_t*C_t<=A_t*D_t`, the full third
  heat-Li formula, and `deBruijnNewmanHeatLiThree 0=liCoefficientCandidate 2`.
- The final sign proof is exact: Lean rewrites Li3 as
  `6*b+(12-8*b)*(c-b^2)+4*(d-b*c)` and combines `B^2<=A*C`, `B*C<=A*D`, and
  `liCoefficientCandidate_zero_re_lt_one`. It proves positive real part and zero imaginary part;
  numerical quadrature is not used.
- The fixed aggregate theorem is `deBruijnNewmanHeat_thirdLi_covariance_endpoint`. Standalone
  compilation is diagnostic-free; exact Targets/TargetChecks, seven selected standard-only axiom
  prints, empty forbidden scans, `git diff --check`, and the 8,695-job full build pass.
  Implementation commit `1b521686d4e8561f01ba98a6ceaa4905ced4d92f` passed public Lean Action CI
  run `29545583372`, build job `87777066173`, in `1m56s`. Classification is
  `DISCOVERY_FORMALIZED`, `hard_gap_delta=0`, and `route_infrastructure_delta=1`. Evidence commit
  `abf5ebf19e3636662a45eed7a5eff9e947c3c3b4` passed public CI run `29545784893`, build job
  `87777708775`, in `2m01s`. The campaign is publicly closed; the RH Goal stays active and returns
  to value-ranked route selection.
- Fresh selection opens `LITERATURE-20260717-H6-HEAT-LI-ALL-INDEX-01`. It must define the full
  derivative-indexed heat Li family, prove pointwise equality with `liCoefficientCandidate` at
  `t=0`, and prove for every `t>=0` the exact equivalence between all-real `H_t` zeros and
  nonnegative real parts of every heat Li coefficient.
- This is materially different from the finite third-coefficient campaign. The fixed endpoint is
  all-index and RH-equivalent at time zero. The restriction `t>=0` reflects the compiled zero-strip
  and half-time all-real inputs; no unsupported negative-time weighted-summability premise is
  hidden. Public preregistration CI must pass before any Lean proof-source edit.
- The preregistration gate passed at commit `e8b611c4e3ab82df78925265c95e4c89ef6d1e29`, public
  Lean Action CI run `29546924877`, job `87781127750`. The complete local implementation is now
  audited in `LeanLab/Riemann/DeBruijnNewmanLiCriterion.lean` and proves a stronger all-real-time
  criterion: affine order-one growth supplies reciprocal-square divisor summability for every real
  `t`, so no negative-time strip premise is needed.
- The module proves the exact all-index paired zero formula, both implications of the Li criterion,
  pointwise time-zero equality, RH theorem compatibility, and the preregistered aggregate endpoint.
  Local gates pass: standalone diagnostic-free compile, exact TargetChecks, selected axioms only
  `propext`/`Classical.choice`/`Quot.sound`, empty forbidden scans, and full 8,696-job build.
  Implementation commit `16437075ed7ceb56becff79c77308d3e33bd1c65` passed public Lean Action CI
  run `29548736988`, build job `87786563205`, in `1m59s`. Classification is
  `KNOWN_CRITERION_HEAT_FAMILY_SPECIALIZATION`, `hard_gap_delta=0`, and
  `route_infrastructure_delta=1`. Evidence commit
  `7e6f4d2e8c78e0c5795842d6ce63169134c1e968` passed public CI run `29548955200`, build job
  `87787209694`, in `2m13s`. The campaign is publicly closed; the RH Goal stays active and will
  resume from value-ranked route selection after this requested rest round.
- The rest round is complete. Fresh route selection opens
  `FALSIFICATION-20260717-H6-XI-LOGCONCAVITY-LEAN-01`, auditing the external Lean certificate
  attached to Gershon's 2026-06-29 Xi-kernel log-concavity v2 preprint at pinned commit
  `7a89db1d546257d8dabefe1ac8b8d4769298a355`.
- The paper's corrected scope leaves the TP2/TP-infinity gap open. The external code nevertheless
  defines log-concavity with conclusion `True`, states the advertised full-kernel theorems as
  `True`, uses custom axioms for both decisive perturbation bounds, and omits the infinite tail in
  its five-term Python verification. Its no-convergence Hurwitz axiom is exactly falsifiable by
  `F_n=1` and `G(z)=z-i`. The preregistered Lean endpoint checks that counterexample and the vacuous
  predicate only; actual Xi-kernel log-concavity, H6-E/G8, and RH are not adjudicated.
- No proof-source edit is allowed before the preregistration commit passes public Lean Action CI.
- The preregistration commit `def8b00d309ef5acc6a0f44a7eb0b47c0db25b01` passed public Lean
  Action CI run `29549982781`, build job `87790283637`, in `1m32s`. The local implementation in
  `XiKernelLogConcavityAudit.lean` proves the exact constant-sequence/`z-i` counterexample and the
  vacuity of the external formal log-concavity predicate.
- Exact Targets/TargetChecks, three selected standard-only axiom prints, empty forbidden scans,
  and the 8,697-job full build pass. Classification is
  `EXTERNAL_FORMALIZATION_REJECTED_AS_PREMISE`, `hard_gap_delta=0`, and
  `route_infrastructure_delta=0`. Actual Xi-kernel TP2 is neither proved nor refuted here; H6-E/G8
  and RH remain open. Implementation commit `8ecb002d1591ae93fbc23ba42c7a487c16c8beb5` passed public
  Lean Action CI run `29550587517`, build job `87792042425`, in `1m50s`. Evidence commit
  `131aff89283644bcabd2f620b94f99dc6ae30843` passed public CI run `29550788159`, build job
  `87792636844`, in `1m55s`. The campaign is publicly closed; the RH Goal returns to value-ranked
  route selection.
- Fresh route selection opens `LITERATURE-20260717-H6-XI-KERNEL-TP2-01`. The exact target is the
  actual full-series inequality `Phi''*Phi-(Phi')^2<0` on `u>=0`, together with all-real-point
  first and second derivative identifications. The primary source is the stronger published
  Csordas-Varga 1988 theorem, in the exact project normalization; Coffey-Csordas 2013 is the
  secondary source. This corrects the 2026 preprint's novelty claim without accepting its
  incomplete tail argument.
- This is an indivisible full-`tsum` endpoint. First-term log-concavity, termwise log-concavity,
  and finite truncations are explicitly rejected as campaign success. Public preregistration CI
  must pass before any Lean proof-source edit. Expected `hard_gap_delta=0`; TP-infinity,
  H6-E/G8, W2/G7, M2/G3, and RH remain open.
- The preregistration commit `36bad715a056e1c626b3ccc8fefae458ddec4110` passed public Lean
  Action CI run `29552030474`, build job `87796448768`. The indivisible endpoint is now complete
  in `XiKernelStrictLogConcavity.lean`: Lean identifies both explicit derivative series at every
  real point and proves the exact full-`tsum` inequality
  `Phi''(u)*Phi(u)-Phi'(u)^2<0` for every `u>=0`.
- The successful proof uses an exact finite weighted log-concavity identity and a uniform
  first-term/geometric estimate. The normalized slope-variance tail is `<63/605<1/8`, hence below
  the first summand's strict negative log-curvature; the uniform finite-prefix bound passes to all
  three infinite sums. The module is diagnostic-free, forbidden scans are empty, exact checks and
  the 8,698-job full build pass, and all selected theorem audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Classification is `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`, and
  `route_infrastructure_delta=1`. Implementation commit
  `1c0c21076d8752c1c9fd623198fb2434fe6cc453` passed public Lean Action CI run `29560492371`,
  build job `87821686793`, in `2m51s`. This closes strict TP2 only; TP-infinity, H6-E/G8, and RH
  remain open. The persistent RH Goal returns to value-ranked route selection.
- Fresh selection opens `FALSIFICATION-20260717-H6-XI-KERNEL-PF5-01`. Michałowski's 2026
  arXiv:2602.20313 and external repository commit
  `675058772f2ba4bf409d114b6082ac9990b78b34` report a negative actual-kernel `5x5` Toeplitz
  determinant at `(u0,h)=(1/100,1/20)`. The external `mpmath.iv` computation was reproduced, but
  it is target-selection evidence only.
- The indivisible Lean endpoint is the exact negative determinant using all nine full
  `deBruijnNewmanPhi` `tsum` values, followed by a source-faithful ordered `not PF5` witness.
  Rational-center determinants, finite truncations, external intervals, and abstract implication
  lemmas do not count as success. Expected `hard_gap_delta=0`; success adds a genuine obstruction
  to PF5/PF-infinity physical-kernel strategies while H6-E/G8 and RH stay open.
- The local endpoint is complete in `XiKernelPF5Falsification.lean`. Lean independently encloses
  all nine full-series entries, proves the exact rational-center determinant below `-1.8e-9`,
  bounds the 120-permutation determinant perturbation below `0.2e-9`, and compiles both
  `xiKernelPF5ToeplitzMatrix_det_neg` and
  `not_isPolyaFrequencyFive_deBruijnNewmanEvenKernel` with strictly increasing source witnesses.
  Selected axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Local classification is `ACTUAL_KERNEL_PF5_FORMALLY_FALSIFIED`, `hard_gap_delta=0`,
  `route_infrastructure_delta=1`, and `obstruction_map_delta=1`. Implementation commit
  `7bdf2b9ab08f2b298d1565921158ff9a199c867a` passed public Lean Action CI run `29565362144`,
  build job `87836632525`, in `2m39s`. The local campaign is publicly closed; the global RH Goal
  stays active and returns to value-ranked route selection.
- Fresh selection then opened `FALSIFICATION-20260717-H6-XI-KERNEL-PF4-01`, targeting the
  source's open global PF4 question in genuinely non-Toeplitz configurations. Preregistration
  commit `b7b4ec77654095c93f3a0b980d42e7ad8784a1fe` passed public Lean Action CI run
  `29566305052`, build job `87839586304`, in `2m12s` before search implementation.
- The registered target-selection suite searched 1 million central, 5 million compact, and
  5 million broad seven-parameter configurations, plus every pair of four-element subsets of
  12-point lattices over eleven steps and six offsets (`16,160,859` finite minors). No robust
  negative determinant was found. All 24 least-conditioned double-negative random/lattice
  candidates became positive under 120-digit Decimal reevaluation; those computations are not
  proof premises.
- The campaign closes locally as `NO_PROGRESS`, with no Lean theorem, no Targets or axiom-audit
  delta, `hard_gap_delta=0`, `route_infrastructure_delta=0`, and `obstruction_map_delta=0`.
  `OBS-H6-XI-PF4-SEARCH-01` records only the exhausted search boundary. Global PF4 is not proved,
  H6-E/G8 and RH remain open, and the persistent Goal returns to fresh route selection after
  closure CI. Closure commit `503b83e35761e87b35fe7db3fb49feab8ea372de` passed public Lean
  Action CI run `29567807097`, build job `87844319595`, in `1m43s`; the campaign is publicly
  closed.
- Census Batch A is complete: H1 fixes the audited critical-zero frontier slightly above `5/12`,
  H2 records the Guth-Maynard `30*(1-sigma)/13` zero-density exponent, and H6 fixes
  `0 <= Lambda <= 0.22` with exact RH edge `Lambda = 0`. See the three
  `research/route_card_H*.md` files and `research/census_batch_A_conjecture_audit_20260717.md`.
- Nine candidates were adversarially audited: four `SHORTLIST_CANDIDATE`, three
  `OPEN_CANDIDATE`, and two rejected density-to-Li transfers. None is a premise and all three
  progress deltas remain zero. Next state is value-ranked `ROUTE_SELECTION`; H10
  Bombieri-Stepanov is the recommended next census card, while direct proof attempts remain open.
- Census/import commit `28874d45a8e14858f6d473edb4b10d1e6d88527a` passed public Lean Action CI
  run `29493531239`, build job `87605050960`, in `2m13s`. Evidence commit
  `746fc1588cd7d217dd31f20f36a434b3bbefd422` passed run `29493755735`, build job
  `87605769894`, in `2m05s`.
- Post-census route selection chooses H6-B as
  `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01`. Its indivisible endpoint is the exact source identity
  `H_0(z)=(1/8)*riemannXi((1+i*z)/2)`. Preregistration commit
  `0eab341f1ad74b866fc942ccb9d89e77cbe51438` passed public Lean Action CI run `29493974202`,
  build job `87606471329`, in `1m55s`.
- H6-B is locally complete as `deBruijnNewmanH_zero_eq_riemannXi`. The implementation explicitly
  defines the source theta kernel `Phi` and cosine transform `H_t`, proves all convergence and
  integration-by-parts steps, converts mathlib's self-dual theta Mellin integral by
  `x=exp(4*u)`, and obtains the exact factor `1/8` without defining `H` through xi.
- The exact module, Targets, TargetChecks, four standard-only axiom prints, empty forbidden scans,
  and the full 8,683-job build pass locally. Classification is `KNOWN_THEOREM_FORMALIZED` with
  `hard_gap_delta=0` and `route_infrastructure_delta=1`. H6-H/H6-E (`Lambda <= 0` or all zeros of
  `H_0` real), W2/G7, M2/G3, and RH remain open. Implementation commit
  `b7824a3b3f3d206617f0a23b124959b6edad937d` passed public Lean Action CI run `29500096845`, build
  job `87626587502`, in `2m37s`. Evidence commit
  `8b9bd1c10000a518ff2f689a69f6431fba412281` passed run `29500378390`, build job `87627536976`,
  in `1m28s`; the campaign is publicly closed and returns to fresh value-ranked route selection.
- Fresh selection chooses `CAMPAIGN-20260717-H6-HEAT-EQUATION-01`. Its indivisible endpoint is:
  for every real `t`, the same source-defined `H_t` is entire in `z`, differentiable in `t`, and
  satisfies `partial_t H_t = -partial_z^2 H_t` with both derivatives identified by the exact
  `u^2`-weighted integral. H6-X and H6-E cannot usefully precede this analytic interface.
- H6-H1 is locally complete in `DeBruijnNewmanHeat.lean`. The reusable majorant proves
  integrability of `(1+u^2)*exp(c*u^2+d*u)*|Phi(u)|` for arbitrary `c>=0,d`; dominated parameter
  integration then gives the exact real-time derivative, complex entire family, second spatial
  derivative, and backward heat equation on all `R x C`.
- The new module is diagnostic-free. Targets and five exact TargetChecks compile; all five selected
  transitive axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden
  scans and `git diff --check` are clean; and the full 8,684-job build passes locally.
- Classification is `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`, and
  `route_infrastructure_delta=1`. H6-H2's all-real-zero predicate, de Bruijn forward preservation,
  threshold existence/closedness, H6-E/G8 (`Lambda<=0`), W2/G7, M2/G3, and RH remain open. Public
  implementation commit `cc62a398160c5865861de0d667b3683ac57694b1` passed Lean Action CI run
  `29504396806`, build job `87641274871`, in `2m9s`. Evidence commit
  `535554372f1e04a3f3c409ae93e0b3e9d7cac04a` passed run `29504634992`, build job `87642099186`,
  in `1m32s`; the campaign is publicly closed. The persistent RH Goal remains active and returns
  to fresh value-ranked route selection.
- Fresh route selection chooses H10-B as
  `CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01`. The new H10 Bombieri-Stepanov card separates
  the characteristic-`p` auxiliary-function point-count argument from its final finite spectral
  step and the number-field transfer gap.
- The indivisible Lean endpoint is: an all-power aggregate bound
  `|sum alpha_i^n|<=C*R^n` forces every finite spectral value into `|alpha_i|<=R`; reciprocal
  product pairing at `R=sqrt(q)` then forces equality. This is known function-field spectral
  infrastructure, not number-field RH.
- The endpoint is locally complete in `FinitePowerSumRigidity.lean`. Simultaneous finite phase
  recurrence sends every nonzero normalized phase near `1` at one arbitrarily large power; all
  real parts are then nonnegative and any value outside radius `R` forces the aggregate norm above
  its assumed bound. Reciprocal product pairing upgrades the radius bound to exact equality.
- The new module is diagnostic-free. Both exact TargetChecks compile; both selected transitive
  axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden scans,
  `git diff --check`, and the full 8,685-job build pass locally. Classification is
  `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`, and `route_infrastructure_delta=1`.
- Preregistration commit `af15b161049aedd65d46fd1f2af1f27e8dc69d44` passed public Lean Action CI
  run `29505635350`, build job `87645529929`, in `1m56s`. The curve point-count theorem, its
  Riemann-Roch/Frobenius construction, and any uniform transfer to the infinite number-field zero
  divisor remain open. Implementation commit `2fc3a7e8efff9636735dcdab0055957a7fdf911f` passed public
  Lean Action CI run `29506928654`, build job `87649987984`, in `1m51s`. Immutable evidence
  commit `54388fae4aea20dc768dd6eeaaee8abcb75316fa` passed run `29507245904`, build job
  `87651088794`, in `2m19s`; the campaign is publicly closed. The persistent RH Goal remains
  active and returns to fresh value-ranked route selection.
- Fresh FALSIFICATION selection chooses `AUDIT-20260717-H6-REVERSE-HEAT-LI-01`. It fixes the
  polynomial heat-Xi family `F_t(s)=(s-1/2)^2-1/16+t/2` and tests whether the heat PDE, reflection,
  nonvanishing at `s=1`, and later critical-line zeros can generically transfer Li positivity
  backward. The indivisible endpoint includes all zeros at time one, an off-line zero at time zero,
  and exact generalized second Li values `448/121` and `-64/9`. This can only eliminate a generic
  H6 mechanism; it does not concern the actual theta-kernel zeros or falsify RH.
- The exact countermodel is locally complete in `H6ReverseHeatLiAudit.lean`. Lean proves
  both-variable entire-ness, reflection, the forward heat PDE, nonvanishing at `s=1` for every real
  `t>=0`, all time-one zeros on the critical line, the time-zero off-line zero `3/4`, and exact
  generalized second Li values `-64/9` and `448/121`.
- The module is diagnostic-free. Its aggregate TargetCheck and four selected axiom prints pass
  with only `propext`, `Classical.choice`, and `Quot.sound`; forbidden scans are empty and the full
  8,686-job build passes locally. Classification is `BRANCH_FALSIFIED`, obstruction
  `OBS-H6-REVERSE-HEAT-LI-01`, and `hard_gap_delta=0`. Preregistration commit
  `215ebcf661a421350d30920ec5aee43518d89559` passed public CI run `29508598381`, build job
  `87655833650`, in `1m30s`. Implementation commit
  `819f3de472c43220895772788911a25e114cc7bd` passed public Lean Action CI run `29509859982`, build
  job `87660158241`, in `2m38s`. Immutable evidence commit
  `b9ebb0d36f4c9d957b26ba089c374172f502907e` passed run `29510451484`, build job `87662213942`,
  in `2m14s`. The campaign is publicly closed as `BRANCH_FALSIFIED`; the persistent RH Goal stays
  active and returns to fresh value-ranked route selection.
- Fresh selection chooses `CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01` in `LITERATURE`
  mode. Its indivisible endpoint compiles the exact `H_0` zero/nontrivial-zeta-zero coordinate,
  inverse coordinate `-i*(2*s-1)`, strict transformed critical strip, and
  `RiemannHypothesis <-> all H_0 zeros are real`.
- This is the definition-alignment subedge of H6-H2, not an unconditional RH result. Expected
  classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
  `route_infrastructure_delta=1`. De Bruijn forward preservation, threshold existence/closedness,
  H6-E/G8, W2/G7, M2/G3, and RH remain open. No Lean proof source is edited before the
  preregistration commit passes public CI. Preregistration commit
  `8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e` passed run `29512089828`, build job `87667820977`,
  in `2m17s`.
- The H6 zero-coordinate framework is locally complete in `DeBruijnNewmanZeros.lean`. Lean proves
  both zero-correspondence directions, the exact inverse coordinate, strict strip, both boundary
  exclusions, and `RiemannHypothesis <-> deBruijnNewmanAllZerosReal 0`.
- The module is diagnostic-free. Its aggregate TargetCheck and boundary witnesses compile; all
  five selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
  forbidden scans are empty; `git diff --check` and the full 8,687-job build pass. Classification
  is `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`, and `route_infrastructure_delta=1`.
  Forward preservation, threshold existence/closedness, H6-E/G8, W2/G7, M2/G3, and RH remain
  open. Implementation commit `0283db6a11ef452a7241e17c535744677272a7d1` passed public Lean
  Action CI run `29513380203`, build job `87672181193`, in `1m59s`. Evidence commit
  `0848fcaf5050d6cc842d53a4154172d7511619f6` passed run `29513928275` on attempt 2, build job
  `87674259193`, in `2m5s`; attempt 1 was an Elan-download SSL reset before project build. The
  campaign is publicly closed and the persistent RH Goal returns to fresh value-ranked route
  selection.

## RH current handoff (2026-07-16, R5 compact C6 formula locally complete)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-COMPACT-C6-EXPLICIT-FORMULA-01` has reached its exact local endpoint
  `symmetrizedCompactLaplaceXi_arithmetic_explicit_formula_sixContDiff`.
- `WeilCompactLaplaceZeroCutoff.lean` now proves the transform derivative identities, inverse-
  sixth decay, and selected xi top-edge limit from `ContDiff R 6` plus compact support.
- `WeilCompactLaplaceArithmeticFormula.lean` removes the previous Schwartz wrapper. Continuity and
  inverse-square Fourier decay give general inversion; inverse-sixth decay gives the first absolute
  Fourier moment. The zero/pole/GammaR/finite-prime identity is otherwise unchanged.
- Both analytic modules compile independently without diagnostics. Exact Targets/TargetChecks,
  five standard-only axiom prints, empty forbidden scans, `git diff --check`, and the full
  8,681-job build pass locally.
- Preregistration commit `540b0ddcbf90a219084f8fdcb80a02ddaad5e277` passed public CI run
  `29467845311`, build job `87524663724`.
- Implementation commit `3e3c677495c592096d7843aa4845e861bc393937` passed public CI run
  `29468797210`, build job `87527584998`, in `2m0s`.
- Evidence commit `94b6be8fc934b3d4909d066b168491389df9afd8` passed public CI run
  `29468980147`, build job `87528144506`, in `1m56s`.
- Classification is `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at compact finite-regularity edge
  `W1c1c2`. Quotient/completeness, full-class regularization, W2/G7, G3/M2, and RH remain open.
- The campaign is publicly closed. Return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; do not
  reopen the old C-infinity endpoint without a strictly stronger target.

## RH current handoff (2026-07-16, R5 compact arithmetic formula publicly closed)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01` has reached its exact fixed endpoint
  as `symmetrizedCompactLaplaceXi_arithmetic_explicit_formula`.
- `WeilCompactLaplaceArithmeticFormula.lean` proves exact Schwartz Fourier inversion with the
  `2*pi` scaling, the physical weight
  `pi*vonMangoldt(n)*(f(log n)+f(-log n)/n)`, absolute interchange, and genuine finite natural
  support from compact support.
- The same module proves selected pole-top decay, the full two-residue integral `2*pi*F(1)`, an
  integrable first absolute moment for every compact vertical branch, GammaR integrability, exact
  finite-edge arithmetic splitting, and all full-line limits.
- The 1,012-line module is diagnostic-free. Exact Targets and TargetChecks, five standard-only
  axiom prints, empty forbidden scans, `git diff --check`, aggregate import, and the full 8,681-job
  build pass locally.
- Classification is `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at the compact W1c1 arithmetic
  subedge. Quotient/completeness, distributional regularization, W2/G7, G3/M2, and RH remain open.
- Preregistration commit `ccebc64b1f3419636461e6fbf968fc55c4f24b8c` passed public CI run
  `29465070647`, build job `87516408926`. Implementation commit
  `55a6406f235a7548bf7f7d53ae5d30014795e9ce` passed run `29466850965`, build job
  `87521708037`, in `1m51s`; evidence commit
  `ed5d03f65bd234f95afb55389b2766d611a3eeab` passed run `29467021669`, build job
  `87522220122`, in `1m43s`.
- The campaign is publicly closed as `BRIDGE_REDUCED`. Return the persistent Goal to fresh
  `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; do not reopen this compact arithmetic subedge without a
  strictly stronger fixed endpoint.

## RH current handoff (2026-07-16, R5 compact Weil zero cutoff publicly closed)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-COMPACT-WEIL-ZERO-CUTOFF-01` is publicly closed as
  `BRIDGE_REDUCED` at its exact preregistered endpoint.
- `tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral` proves the selected-height xi
  zero-side limit for the reflection symmetrization of every smooth compactly supported
  additive-log function and every `c>1`.
- Lean derives whole-plane transform differentiability, exact reflection, complete
  multiplicity-bearing divisor summability, arbitrary compact-support integration by parts,
  inverse-sixth-power decay on the full rectangle strip, and `O(R^(-2))` top-edge vanishing.
- The 373-line module, exact Targets and TargetChecks, five selected axiom prints containing only
  `propext`, `Classical.choice`, and `Quot.sound`, empty forbidden scans, `git diff --check`, and
  the full 8,680-job build pass locally.
- `hard_gap_delta=1` applies only to the fixed W1c1 compact zero-side subedge. The generic compact
  arithmetic prime, pole, and archimedean evaluation, W2/G7, G3/M2, and RH remain open.
- Preregistration commit `e70201cb71b0909ae3f7b798336931e0bd9f32ee` passed public Lean Action CI
  run `29463597042`, build job `87511970349`. Implementation commit
  `0e6451944ee1edb2d76d67f4fe097de2aa19ad17` passed run `29464308480`, build job
  `87514106839`, in `2m10s`; evidence commit
  `6c2f3ab912097e4e5b325e9d0c27d43438a29d99` passed run `29464469804`, build job
  `87514591845`, in `1m43s`.
- The campaign is publicly closed at its exact endpoint. Return the persistent RH Goal to fresh
  `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; do not reopen this zero-side cutoff without a strictly
  stronger endpoint.

## RH current handoff (2026-07-16, R5 Gaussian prime-kernel sign audit publicly closed)

- The persistent RH Goal remains active. Fresh DISCOVERY route selection admits
  `AUDIT-20260716-R5-GAUSSIAN-PRIME-KERNEL-SIGN-01`.
- `exists_pos_symmetricGaussianPrimeKernelMatrix_indefinite` uses the actual `n=2` symmetric
  Gaussian von-Mangoldt weight and proves that one explicit two-shift kernel matrix is neither
  positive nor negative semidefinite.
- Lean checks width `(log 2)^2/16`, shifts `0, log 2`, `vonMangoldt 2 = log 2`, exact
  diagonal/off-diagonal formulas, a negative `(1,-1)` direction, and a positive diagonal.
- The 251-line module, Targets, typed witness, four standard-only axiom prints, scans, aggregate
  import, `git diff --check`, and full 8,679-job build pass locally.
- Classification is `BRANCH_ELIMINATED` for termwise semidefinite local-prime assembly only.
  Complete local cancellation, generic W1c1, W2/G7, and RH remain open; `hard_gap_delta=0`.
- Implementation commit `01ea63517670a81b8c640de1135dec62d44436b9` passed public Lean Action CI
  run `29462677629`, build job `87509304721`, in `1m54s`; evidence commit
  `af7848aea84287329ce50900d5e425538165baaa` passed run `29462828680`, build job `87509738532`,
  in `1m58s`. Resume only through fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## RH current handoff (2026-07-16, R5 compact Laplace separator publicly closed)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-COMPACT-LAPLACE-SEPARATOR-01` is publicly closed at its exact
  preregistered endpoint in `LeanLab/Riemann/WeilCompactLaplaceSeparator.lean`.
- `exists_compactSupport_xiDivisor_laplace_tsum_separator` constructs, for every selected
  multiplicity-bearing xi-divisor index and every `epsilon>0`, a smooth compactly supported
  log-line function whose bilateral Laplace transform is one at the selected value, is absolutely
  summable on the complete divisor, and has strict total norm below `epsilon` over all different
  zero values.
- Lean checks translation and convolution covariance, twofold integration-by-parts decay, complete
  reciprocal-square domination, finite fixed-superlevel annihilation, real-translate polynomial
  realization, and compact convolution-power suppression. Equal-value multiplicity copies are
  protected.
- The formal module, Targets, TargetChecks, five selected axiom prints, repository scans, and the
  full 8,678-job build pass locally; the prints contain only `propext`, `Classical.choice`, and
  `Quot.sound`. The implementation and evidence commits each pass independent public CI.
- Classification is `KNOWN_MECHANISM_RECONSTRUCTED`; this is one unconditional W1 reverse-
  separation component, not a generic explicit formula, unconditional Weil positivity, G7/W2,
  or RH. `hard_gap_delta=0`.
- Implementation commit `6d12bad98b80c34217757df01943509965a64781` passed public Lean Action CI
  run `29461298466`, build job `87505125618`, in `1m47s`; evidence commit
  `941756c2e7e0b4da8f765dc7187e4be703af36c8` passed run `29461494669`, build job `87505716647`,
  in `2m22s`. Resume only through fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## RH current handoff (2026-07-16, R5 fixed-width Gaussian criterion publicly closed)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-FIXED-WIDTH-01` is publicly closed at its exact endpoint.
- For every preassigned `a0>0`,
  `riemannHypothesis_iff_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg` proves that RH is
  equivalent to nonnegativity of every finite real Gaussian-Weil arithmetic quadratic at exactly
  width `a0` and contour parameter `c=2`.
- The proof realizes every width increase by finite Rademacher packets with multiplier
  `cosh(sqrt(c/n)*z)^n`, proves the complex power limit, obtains a strip-uniform norm bound, and
  applies dominated convergence over the complete multiplicity-bearing xi divisor. The existing
  off-line separator is strengthened above an arbitrary width threshold and transferred back to
  the fixed base width.
- The standalone module is diagnostic-free. Exact Targets/TargetChecks, five standard-only axiom
  prints, empty forbidden/scratch/resource scans, `git diff --check`, and the 8,677-job full build
  pass locally.
- Implementation `f56b70478ab552802cac719b8e9af0f56fc44b1d`, evidence
  `f93e73cbdd71785a28cc2b05f8ef2b0390b358cf`, and closure
  `8b45a091aa4f16e348a2cd8b73e949480f446508` each passed public Lean Action CI runs
  `29458594435`, `29458788171`, and `29458987040`.
- This is an RH-equivalent parameter compression, not unconditional positivity or RH.
  `hard_gap_delta=0`; W2/G7 remains open. Resume only through fresh
  `INDEPENDENT_AUDIT -> ROUTE_SELECTION` and do not reopen width compression without a strictly
  stronger endpoint.

## RH current handoff (2026-07-16, R5 Gaussian arithmetic publicly complete)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-EXPLICIT-FORMULA-01` has reached its exact fixed endpoint in
  `LeanLab/Riemann/WeilGaussianExplicitFormula.lean`.
- `gaussianXi_arithmetic_explicit_formula` proves unconditionally, for `a>0` and `c>1`,
  `pi*zero_tsum = 2*pi*exp(a/4) + GammaR_integral - vonMangoldt_gaussian_tsum` with analytic zero
  multiplicity and all prime powers.
- The module separately proves the exact one-term Fourier-Gaussian transform, absolute
  series/integral interchange, summability of the explicit prime weight, GammaR full-line
  integrability from a checked digamma bound, and an independent two-pole residue evaluation.
- Exact TargetChecks pass. Five selected transitive axiom prints contain only `propext`,
  `Classical.choice`, and `Quot.sound`; the new module builds without warnings. All forbidden-token,
  declaration, and resource-option scans are empty, `git diff --check` passes, and the 8,670-job
  full project build succeeds.
- The campaign is locally complete as `BRIDGE_REDUCED`.
- Implementation commit `6c65019d9de2d31127dd3bf8389994207c17dcb5` passed public Lean Action CI
  run `29441160498`, build job `87440149741`, in `2m33s`.
- Evidence-backfill commit `fa5fdc5aefd4dd3e99966cc1e0fcca62293e9600` passed public Lean Action CI
  run `29441452307`, build job `87441220281`, in `1m28s`. The campaign is publicly closed as
  `BRIDGE_REDUCED`; return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.
- This closes only one fixed-test arithmetic W1c subedge. Generic test classes, singular
  regularization, Weil positivity, and RH remain open; do not mark the persistent Goal complete.

## RH previous handoff (2026-07-16, R5 Gaussian height-limit publicly complete)

- The persistent RH Goal remains active. Campaign
  `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-HEIGHT-LIMIT-01` is locally complete as `BRIDGE_REDUCED`.
- `LeanLab/Riemann/WeilGaussianHeight.lean` proves that for every `a>0`, `c>1`, there are symmetric
  zero-free heights `T_n -> infinity` along which the Gaussian-weighted right-vertical `xi'/xi`
  integrals tend to `pi` times the absolute multiplicity-bearing Gaussian zero `tsum`.
- The mechanism uses only reciprocal-square Hadamard summability: it gives absolute Gaussian zero
  summability, an `O(R^2)` near-zero count, quantitative height separation, and an `O(R^4)`
  horizontal log-derivative bound absorbed by `exp(-a*R^2)`.
- The exact endpoint is
  `exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral`. The new module is warning-free;
  exact Targets, five standard-only axiom prints, forbidden scans, `git diff --check`, and the
  8,669-job full build pass locally.
- This closes only one fixed-test W1c1 zero-side height-limit subedge. Prime/archimedean evaluation,
  generic test-class extension, W1c2 regularization, W2 positivity, and RH remain open.
- Both public evidence gates now pass. Return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`
  without reopening this fixed endpoint.
- Implementation commit `00410cc2a6919acfa5835b121c47489c5105e0de` passed public Lean Action CI
  run `29436179027`, build job `87423295204`, in `2m23s`.
- Evidence-backfill commit `2292801d710a1a95857de69a92498c39ae79d0d3` passed public Lean Action CI
  run `29436471220`, build job `87424276428`, in `1m57s`. The campaign is publicly closed as
  `BRIDGE_REDUCED`.

## RH current handoff (2026-07-15, R1 q=2 Baez-Duarte criterion locally complete)

- The persistent RH goal remains active. `CAMPAIGN-20260715-R1-BAEZ-DUARTE-QTWO-01` closes locally
  as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0`.
- `LeanLab/Riemann/BaezDuarteQTwo.lean` constructs `chi *_M chi` and `chi *_M rho_n` in complex
  `L2(0,infinity)`, with exact Mellin transforms `1/s^2` and
  `n^(-s) * (-zeta(s)/s^2)` and the exact reciprocal tail.
- The bounded critical-line multiplier by `1/s`, transported through Fourier-Mellin, maps the
  existing q=1 target and every generator to the q=2 objects and proves the RH-forward direction.
- The reverse proof does not invert that multiplier. It independently combines finite-sum Mellin
  vanishing at a zeta zero, local Cauchy-Schwarz, full-line closure approximation, exact tail-moment
  control, and zero reflection.
- The exact final theorem is
  `riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure`.
- New-module compilation, exact Targets, eight standard-only axiom prints, five empty forbidden
  scans, `git diff --check`, the 8,608-job module build, and the 8,668-job full build pass locally.
- This formalizes a known RH equivalence; unconditional target-closure membership and RH remain
  open. Next: publish, verify public CI, backfill immutable evidence, and start a fresh route audit.
- Implementation commit `90313d83210bdfe0aca8b62153240d51e0c924b1` passed public Lean Action CI
  run `29430307834`, build job `87403316754`, in `2m20s`.
- Evidence-backfill commit `b5b8f0f3688cfef8d310ecc503d7f829dbc8e646` passed public Lean Action CI
  run `29430594438`, build job `87404277090`, in `1m26s`. The campaign is publicly closed; begin a
  fresh independent route audit while keeping the persistent RH Goal active.

## Previous RH handoff (2026-07-15, R5 Weil explicit integrand publicly closed)

- The persistent RH goal remains active. `CAMPAIGN-20260715-R5-WEIL-EXPLICIT-INTEGRAND-01`
  closes as `BRIDGE_REDUCED`: one source-level W1c subedge closes, while RH progress is
  unchanged.
- `LeanLab/Riemann/WeilExplicitIntegrand.lean` proves on `Re(s)>1` the exact identity
  `logDeriv xi = 1/s + 1/(s-1) + logDeriv GammaR - L(vonMangoldt)`.
- The proof establishes every factor's nonvanishing and differentiability before taking
  logarithmic derivatives. It uses Mathlib's absolutely convergent von Mangoldt L-series theorem,
  not the explicit formula or RH.
- The final theorem identifies the same integrand with the existing multiplicity-bearing
  genus-one Hadamard zero sum. This compiles the zero/pole/archimedean/prime integrand bridge.
- Exact targets, all six public axiom audits, forbidden scans, `git diff --check`, standalone
  builds, and the 8,666-job full build pass. Every new theorem uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Implementation commit `89d4dd12ebedc75c13261a0d43a9254b5931c30d` passed public Lean Action CI
  run `29417432562`, build job `87359008630`, in 1m47s.
- Evidence-backfill commit `1b405639a4e28c72fc1e2484259c047ad95ed0b2` passed public Lean Action CI
  run `29417710278`, build job `87359940112`, in 1m31s. The campaign is publicly closed.
- W1c1 test-function integration and contour cutoff, W1c2 regularization/covariance extension,
  W2 positivity, and RH remain open. Next: publish this final closure log, verify clean
  synchronization, and return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Previous RH handoff (2026-07-15, R3/R5 Li-Weil Gram publicly closed)

- The persistent RH goal remains active. `CAMPAIGN-20260715-R3-R5-LI-WEIL-GRAM-01` closes
  as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0`.
- `LeanLab/Riemann/LiWeilGram.lean` defines the reflection-averaged, multiplicity-bearing Li-test
  Gram kernel. Each term reduces to compiled symmetry-paired Li terms before tsum, so no raw
  conditionally convergent Li zero sum is admitted.
- The exact matrix is
  `lambda_n + lambda_m - (if n=m then 0 else lambda_(dist(n,m)-1))` in project indexing, and every
  diagonal entry is `2 * liCoefficientCandidate n`. Low-index `(0,1)` and `(0,2)` checks compile.
- For every finitely supported real coefficient family, RH identifies the quadratic form with a
  summable divisor series of `Complex.normSq`. Conversely, `Finsupp.single n 1` recovers every Li
  real-part inequality, giving the exact quadratic positivity iff RH.
- Exact targets, all 15 public axiom audits, forbidden scans, `git diff --check`, and the 8,665-job
  full build pass. Every new theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Implementation commit `2317143e73e1d788d65dcdff9b609a98f8ac60b2` passed public Lean Action CI
  run `29415448733`, build job `87352327801`, in 1m48s.
- Evidence-backfill commit `89fb947b493c8fd315bbe67a5be8c09fc99cdfa3` passed public Lean Action CI
  run `29415725269`, build job `87353260131`, in 1m35s. The campaign is publicly closed.
- This is an RH-equivalent known-theorem formalization. It does not prove complex Hermitian
  extension, W1c, W2, or RH. Next: publish this final closure log, verify clean synchronization,
  and return to `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Previous RH handoff (2026-07-15, R5 Weil strip class publicly closed)

- The persistent RH goal remains active. `CAMPAIGN-20260715-R5-WEIL-STRIP-CLASS-01` closes locally
  as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` for RH.
- `LeanLab/Riemann/WeilStripClass.lean` defines the symmetric positive-width Mellin strips and the
  physical predicate `IsWeilStripAdmissible`: pointwise convergence on the closed strip,
  analyticity on the open strip, continuity and a finite uniform bound on the closed strip.
- The class is closed under zero, addition, complex scalar multiplication, Weil involution,
  physical conjugation, conjugate star, multiplicative convolution, and self-star autocorrelation.
  Conjugation analyticity is proved through `conj o mellin(f) o conj`; convolution closure uses the
  compiled W1a Mellin product.
- Exact target witnesses and all 16 public axiom audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. Standalone compilation, forbidden scans,
  `git diff --check`, and the 8,664-job full build pass locally.
- Implementation commit `335d6dfa175a345555aaa408b5581ed743d2abf7` passed public Lean Action CI
  run `29412820223`, build job `87343685661`, in 1m42s.
- This closes W1b's physical algebra core only. Raw-function metric separation,
  quotient/uniqueness/completeness, density, W1c's complete explicit formula, W2 positivity, and
  RH remain open.
- Evidence-backfill commit `4b1d549504ae1965fb8cd34e314a4c682ca662a2` passed public Lean Action CI
  run `29413062276`, build job `87344475624`, in 1m46s. The campaign is publicly closed. Publish
  this closure log, verify clean synchronization, and then return to
  `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Previous RH handoff (2026-07-15, R5 Weil convolution publicly closed)

- The persistent RH goal remains active. Independent audit admitted one same-route successor from
  Lagarias (A.7): `CAMPAIGN-20260715-R5-WEIL-CONVOLUTION-01` closes locally as
  `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` for RH.
- `LeanLab/Riemann/WeilConvolution.lean` defines physical multiplicative convolution using `dy/y`
  and proves its logarithmic lift is Mathlib additive Bochner convolution.
- Exact pointwise `MellinConvergent` assumptions on both inputs imply convergence of the
  convolution and `M(f *_M g)(s)=M(f)(s)M(g)(s)`; no compact-support, continuity, or strip premise
  is added.
- Combining the product with `weilStar` gives the exact `1-conj(s)` factor. On the critical line,
  self-star autocorrelation compiles to `Complex.normSq`.
- Exact target witnesses and all public axiom audits pass with only `propext`, `Classical.choice`,
  and `Quot.sound`. Standalone, scans, `git diff --check`, and the 8,663-job full build pass locally.
  Implementation commit `90874a87a89ee371719c2f50f5cc02eaae8a5040` passed public Lean Action
  CI run `29410786209`, build job `87337104802`, in 1m46s.
- This closes W1a only. The analytic-strip test class, complete explicit formula, distributional
  convergence, density, Weil positivity, and RH remain open.
- Evidence-backfill commit `30a816118acf74a0ab9bead03b7541d6929dcfe3` passed public Lean Action CI
  run `29410987990`, build job `87337750370`, in 1m29s. The campaign is publicly closed. Next:
  publish this closure log, verify clean synchronization, then return to
  `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Previous RH handoff (2026-07-15, R5 Weil test algebra publicly closed)

- The persistent RH goal remains active. After the R3 Li criterion closed, route selection moved
  to the distinct R5 explicit-formula family. `CAMPAIGN-20260715-R5-WEIL-TEST-ALGEBRA-01` closes
  locally as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0`.
- `LeanLab/Riemann/WeilTestAlgebra.lean` formalizes Lagarias Appendix A (A.1)-(A.2):
  `f_tilde(x)=x^(-1)f(x^(-1))`, pointwise involutivity on `0<x`, and
  `M(f_tilde)(s)=M(f)(1-s)` using Mathlib's actual Mellin integral.
- Lean separately proves exact preservation of `MellinConvergent`, preventing the Bochner
  integral's nonintegrable-value convention from masquerading as analytic convergence. A compiled
  counterexample shows why the total pointwise involution theorem cannot include `x=0`.
- The conjugate star satisfies `M(f_star)(s)=conj(M(f)(1-conj(s)))`; on the critical line it is
  conjugation at the same spectral point. The endpoint formulas at `s=0,1` swap exactly.
- Exact target witnesses and all selected axiom audits pass; dependencies are only `propext`,
  `Classical.choice`, and `Quot.sound`. Standalone compilation, the 8,662-job full build, forbidden
  scans, and `git diff --check` pass locally. Implementation commit
  `24621330af4a24269a1748c5b3a4f924c16a7768` passed public Lean Action CI run `29409014307`,
  build job `87331366564`, in 2m27s.
- This is not the explicit formula or a positivity theorem. Multiplicative convolution closure,
  a complete zero/prime/pole/archimedean formula, density, and unconditional Weil positivity remain
  open. The RH assumption frontier is unchanged.
- Evidence-backfill commit `1c9e7fe27536bda8e04aa7e7bda2af1d110fe61c` passed public Lean Action
  CI run `29409249934`, build job `87332127195`, in 1m33s. The campaign is publicly closed. The
  successor state is `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Previous RH handoff (2026-07-15, R3 reverse Li criterion publicly closed)

- The persistent RH goal remains active. `CAMPAIGN-20260715-LI-REVERSE-BOMBIERI-LAGARIAS-01`
  closes locally as `KNOWN_THEOREM_FORMALIZED_WITH_PROJECT_SPECIALIZED_PHASE_ARGUMENT`, with
  route-local `hard_gap_delta=1`.
- `LeanLab/Riemann/LiReverseCriterion.lean` proves the exact transform geometry, reflection-
  invariant orbit radius, finite radius superlevels, finite-product phase recurrence, paired main-
  term negativity, fixed-weight complement domination, and polynomial-versus-exponential tail
  decay.
- The key implementation refinement uses any off-line orbit radius `R0>1` and threshold
  `c=(1+R0)/2`. It aligns the entire finite `radius>=c` set and controls everything outside by
  `m^2*c^m`; no global maximal zero, zero enumeration, or far/near zero-count split is needed.
- Lean proves `exists_liCoefficientCandidate_re_neg_of_divisorZero_re_ne_half`: every off-line xi
  divisor zero forces some project Li coefficient to have strictly negative real part.
- The preregistered endpoints
  `riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg` and
  `riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg` both compile. The project index
  is classical `lambda_(n+1)`.
- This is known Bombieri-Lagarias/Li criterion mathematics, not an unconditional proof of RH or of
  all-index positivity. The global RH assumption frontier remains open.
- Standalone compilation, exact TargetChecks, eight standard-only axiom checks, empty forbidden
  scans, `git diff --check`, and the 8,661-job full build pass. Implementation commit
  `22cedfa17788fec546b91b9dc78452de52d87e64` passed public Lean Action CI run `29406614212`, build
  job `87323510543`, in 2m31s. Evidence-backfill commit
  `48385f277c83b06a5d72aee83d06d0f4b31623d1` passed public run `29406932411`, build job
  `87324549428`, in 1m21s. The campaign is publicly closed.
- Next state after publication is `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; the persistent Goal must
  remain active.

## Previous RH handoff (2026-07-15, R3 symmetry-paired Li formula locally verified)

- The persistent RH goal remains active. `CAMPAIGN-20260715-LI-SYMMETRIC-ZERO-01` closes locally
  as `BRIDGE_REDUCED`, with route-local `hard_gap_delta=2` and no change to the RH assumption
  frontier.
- `LeanLab/Riemann/LiSymmetricZeroFormula.lean` constructs the multiplicity-preserving divisor
  involution `rho |-> 1-rho`. It also compiles the harmonic countermodel rejecting unpaired raw
  summability and the off-critical pair `rho=1/4`, `m=2`, whose average is `-32/9`.
- For every index, Lean proves the reflected finite compensated contribution equals the raw Li
  term plus its reciprocal correction. Averaging the existing summable series along the exact
  equivalence proves summability of the symmetry-paired raw term.
- The xi functional equation at `0` and `1`, together with the degree-at-most-one Hadamard
  polynomial, cancels both remaining artifacts. The unconditional endpoint is
  `liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm` for every project index
  `n`, corresponding to classical `lambda_(n+1)`.
- Under RH, `1-rho=conj(rho)` and each paired term is exactly half a complex norm square.
  `RiemannHypothesis.liCoefficientCandidate_im_eq_zero` and
  `RiemannHypothesis.liCoefficientCandidate_re_nonneg` close the full forward direction.
- This is known Li/Bombieri-Lagarias mathematics formalized and aligned with the project, not a
  new proof of RH. The reverse all-index positivity-to-RH implication remains unproved.
- Standalone/module checks, exact TargetChecks, the 8,660-job full build, forbidden scans, and
  `git diff --check` pass. Eight audited declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`. Implementation commit `4168188f70e2cb6f2e47c65334a8326dabd23edc` is public;
  Lean Action CI run `29401711930`, build job `87307546611`, succeeded in 1m48s.
- Evidence-backfill commit `81c53eb62acf3500aee00061e5ee0ff8cc6eb13e` passed public Lean Action
  CI run `29401901693`, build job `87308160283`, in 1m55s. The campaign is publicly closed under
  its preregistered `BRIDGE_REDUCED` condition.
- Next state after public verification is `INDEPENDENT_AUDIT -> ROUTE_SELECTION`. A further R3
  campaign must source-audit and preregister the reverse Li/Bombieri-Lagarias large-index argument,
  or select a distinct route family.

## Previous RH handoff (2026-07-15, R3 all-index compensated Li zero formula verified)

- The persistent RH goal remains active. `CAMPAIGN-20260715-LI-ZERO-FORMULA-01` closes locally as
  `BRIDGE_REDUCED`, with route-local `hard_gap_delta=1` and no change to the RH assumption frontier.
- `LeanLab/Riemann/LiZeroFormula.lean` proves the exact all-index Leibniz expansion from the
  derivative-defined project Li family, whose index `n` is classical `lambda_(n+1)`.
- For every positive derivative order, Lean proves compact-local uniform summability of the
  multiplicity-bearing zero-term series. The far-zero M-test is dominated by
  `k! * 2^(k+1) * |rho|^(-2)`; finitely many near zeros are handled separately.
- Lean applies `iteratedDerivWithin_tsum` on the proved open xi nonzero set containing `1`, retains
  the genus-one `1/rho` compensation at order zero, and derives every iterated log-derivative from
  one fixed degree-at-most-one Hadamard polynomial and the compensated zero series.
- `exists_liCoefficientCandidate_eq_hadamard_zero_formula` combines these facts for every index
  without an extra premise. This is known-theorem formalization/project alignment, not new
  mathematics. No raw ordered zero sum, positivity, Li/RH equivalence, or RH is claimed.
- Standalone/module checks, exact TargetChecks, standard-only axiom output, the 8,659-job full
  build, forbidden-token scans, and `git diff --check` pass. Implementation commit
  `88037ad4423c430809f3f381fd354699dc307827` is public; Lean Action CI run `29397368460`, build
  job `87293810332`, succeeded in 1m48s. Evidence-backfill commit
  `286bd1fa12d0009d4fe86bd9149219bedbb61470` passed run `29397552248`, build job
  `87294383278`, in 1m32s.
- Next state after publication is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. Further R3 work
  requires a precise raw-zero-sum convergence/normalization edge, an exact Li/RH equivalence, or an
  equally global successor. Fixed-index coefficient calculations remain inadmissible.

## Previous RH handoff (2026-07-15, R3 global xi Hadamard bridge verified)

- The persistent RH goal remains active. `CAMPAIGN-20260715-XI-HADAMARD-01` closes locally as
  `BRIDGE_REDUCED`, with route-local `hard_gap_delta=3` and no change to the RH assumption frontier.
- The exact 61-module custom dependency closure ending at
  `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard` is snapshotted from
  pinned Apache-2.0 commit `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`. Twenty-four modules
  were already present; 37 were added. All 61 remain byte-identical to the pinned checkout and the
  terminal module compiles with 3,683 jobs.
- `LeanLab/Riemann/LiHadamard.lean` proves the project xi equals `Complex.riemannXi`, aligns the
  Hadamard divisor-index fiber exactly with `riemannXiZeroMultiplicity`, and proves index values
  are exactly `IsNontrivialZero`.
- Lean transports order-one entire growth, squared reciprocal zero summability, the no-origin
  genus-one global Hadamard product, and the compensated log-derivative zero sum at every point
  that is not a nontrivial zero.
- This is existing-theorem formalization and project alignment, not a new mathematical result.
  The degree-at-most-one exponential polynomial remains in the product. No raw genus-zero sum,
  all-index Li derivative-to-zero identity, Li positivity, or RH is claimed.
- Exact TargetChecks, standard-only axiom output, the 8,658-job full build, source scans, closure
  byte audit, and `git diff --check` pass. The seven selected declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. Implementation commit
  `406fef704202777a6510a9eddd69a402075d31f6` is public; Lean Action CI run `29394659365`, build
  job `87285308740`, succeeded in 3m12s. Evidence-backfill commit
  `ffbd4967d3e220593bbbcaa1c63ffbe37dea4282` passed public run `29394898804`, build job
  `87286063151`, in 1m28s.
- Next state is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. A further R3 campaign must target an
  exact all-index derivative-defined Li family and derivative-to-zero bridge, or another equally
  precise global edge. Fixed low-index coefficient calculations remain rejected.

## Previous RH handoff (2026-07-15, R3 xi zero-divisor implementation verified)

- The persistent RH goal remains active. After closing the R1 sparse mechanism, route selection
  moved to the distinct R3 Li/Weil family. `CAMPAIGN-20260715-XI-DIVISOR-01` closes as
  `BRIDGE_REDUCED`, with `hard_gap_delta=1` for the fixed divisor/local-multiplicity prerequisite
  and no change to the global RH assumption frontier.
- `LeanLab/Riemann/LiZeroDivisor.lean` proves that negative-even trivial zeta zeros are not zeros of
  `riemannXi`, strengthens the zero bridge to
  `IsNontrivialZero s <-> riemannXi s = 0`, and excludes infinite local analytic order by the
  identity theorem and `riemannXi 1 = 1/2`.
- The new `riemannXiZeroDivisor` is globally locally finite, takes exactly the integer cast of the
  natural analytic zero multiplicity, has support exactly `{s | IsNontrivialZero s}`, meets every
  compact set finitely, and preserves multiplicity under `s |-> 1-s`.
- This is known-structure project alignment, not a new mathematical result. No canonical zero
  enumeration, Hadamard product, convergent zero sum, Li positivity, or RH is claimed.
- Standalone/module checks, exact TargetChecks, the 8620-job full build, forbidden scans, and
  `git diff --check` pass. The six new audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. Implementation commit
  `15e30c800e39d904b1623d5e8efcb40864e18655` is public; Lean Action CI run `29392983909`, build
  job `87280263113`, succeeded in 2m2s.
- Next state is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. Continuing R3 requires a precise
  order-growth, canonical-product, or zero-summability edge; do not return to low-index Li
  coefficient calculations.

## Previous RH handoff (2026-07-15, sparse target branch elimination published)

- The persistent RH goal remains active. `CAMPAIGN-20260715-SPARSE-OBSTRUCTION-01` closes as
  `BRANCH_ELIMINATED`, with `hard_gap_delta=0` and the assumption frontier unchanged.
- `LeanLab/Riemann/M2SparseObstruction.lean` constructs the preregistered three-interval complex
  `L2` witness. Lean proves its pairing with every normalized `(2^24)^j` kernel is zero, while its
  pairing with `baezDuarteComplexTargetL2` is exactly `1/9`.
- Consequently `baezDuarteComplexTargetL2_not_mem_sparseGramKernelClosure` proves that the exact
  target is not in this sparse closed span. This excludes only the lacunary subfamily and does not
  alter the RH-equivalent closure theorem for the full natural family.
- Standalone/module builds, exact TargetChecks, the 8619-job full build, forbidden scans, and
  `git diff --check` pass. The three new audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. Implementation commit
  `c2e6f086b30fc54b5e0ed6ab2782bf5ef9283a85` is public; Lean Action CI run `29391437206`, build
  job `87275634635`, succeeded.
- Preserve the previous sparse lower-frame theorem as useful auxiliary geometry, but do not revisit
  target coupling for `(2^24)^j` without a genuinely different endpoint. Return to
  `ROUTE_SELECTION` now and choose a different route family.

## Previous RH handoff (2026-07-15, sparse Gram campaign implementation published)

- The persistent RH goal remains active. Campaign `CAMPAIGN-20260715-GRAM-01` completed its one
  admitted proof attempt with result `AUXILIARY_PROPERTY_PROVED` and `hard_gap_delta=0`.
- `LeanLab/Riemann/M2GramGeometry.lean` proves for every `c : Nat →₀ Complex` the exact bound
  `(1/40) * sum |c_i|^2 <= ||sum c_i*u_((2^24)^i)||^2` on the real source-aligned kernels packaged
  in complex `L2(0,infinity)`.
- The proof includes the physical `1/24` diagonal lower bound, the three-region logarithmic
  off-diagonal envelope, a `4/297` row-sum bound, and the finite complex quadratic-form argument.
  Numerical experiments are not premises.
- A typed `EuclideanSpace Real (Fin 2)` witness proves that positive-definite finite Gram data can
  coexist with a nonzero orthogonal target. Therefore finite Gram invertibility alone remains
  rejected as a target-closure mechanism.
- Exact `TargetChecks` and transitive axiom audit pass; audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`. The 8618-job full build, forbidden scans, and
  `git diff --check` pass. Implementation commit
  `f433644b5c9ad7a21ccabbc87b03ef6e8b3a1284` is public; Lean Action CI run `29390161766`, build
  job `87271625044`, succeeded.
- No target-closure membership or residual convergence is proved. M2/G3 was historically unselected (open under V4.1) and the RH
  assumption frontier is unchanged. Do not spend the next campaign optimizing this constant or
  adding generic Gram wrappers. Enter `ROUTE_SELECTION` and require a precise target-coupling
  mechanism or select another route family.

## Previous RH handoff (2026-07-15, Discovery Protocol V3 route selection)

- The persistent RH goal is active. Commit `5d75abc` remains valid, but its `STOP` applies only to
  the exhausted automatic 2025-2026 recent-literature screening campaign. Local campaign stops now
  enter `ROUTE_SELECTION`; they do not stop the global goal.
- Wong arXiv `2310.03972v5` and Carvill arXiv `2510.18132` remain rejected. Preserve their Lean
  counterexamples and do not reopen those proof branches.
- `research/discovery_protocol_v3_20260715.md` records global persistence, campaign stages,
  conjecture admission, anti-cycling, and progress accounting. Its former numerical campaign
  length is superseded by V4.1.
- `research/route_portfolio.md` compares five route families. The selected campaign is
  `CAMPAIGN-20260715-GRAM-01`, exact Baez-Duarte Gram/projection geometry.
- `research/m2_gram_route_prereg_20260715.md` registers five candidate mechanisms, adversarial
  checks, nearest literature, and exactly one selected proof candidate: an explicit sparse lower
  frame bound for normalized kernels at indices `(2^24)^j`.
- All current eigenvalue and quadrature observations are `NUMERICAL_ONLY`. No new mathematical
  premise had been admitted and no Lean theorem had yet been added in this historical campaign;
  its `hard_gap_delta=0`. M2/G3 is open under V4.1.
- Next work is one indivisible Lean proof attempt for the registered sparse bound. C1/C3 inputs
  must stay in that batch; partial helpers are not separate research loops.

## Previous RH handoff (2026-07-15, M2/G3 automatic literature campaign stopped)

- M0, M1, G1, G2, D, and G4/B1 remain complete; M2/G3 was historically unselected (open under V4.1). No unconditional proof of
  RH or target closure membership is claimed.
- Audit `AUDIT-20260715-M2-G3-03` screened the remaining current 2025-2026 candidates. Iyer leaves
  the residual-covariance/Hilbert approximation bridge open; the Colombeau paper proves another
  RH equivalence; Bhattacharjee et al. use a mismatched `{x/k}` carrier and disclaim an RH proof;
  the dyadic project is conditional and numerical.
- No candidate supplied an unconditional estimate on the exact M0/M1-aligned carrier, so no Lean
  target or mathematical source edit was admitted. Classification: `NO_PROGRESS`, with
  `hard_gap_delta=0` and the assumption frontier unchanged. `git diff --check` and the unchanged
  8617-job project build pass.
- Audits M2-G3-01, M2-G3-02, and M2-G3-03 produced zero hard-gap delta and triggered a local
  `STOP` under the then-current v2 rule. V4.1 abolishes that numerical rule: M2/G3 is open, and
  re-entry requires only a preregistered materially new attack angle.
- This is a protocol stop, not a proof that future research is impossible and not a `blocked`
  status for the persistent broad goal.
- Governance commit `6bdbd1f9a459edb1b0baa7d3568b44605f0d4fc6` passed public Lean Action CI
  run `29384810340`, build job `87255750317`, in 1m24s.

## Previous RH handoff (2026-07-15, Carvill branch falsified)

- M0, M1, G1, G2, D, and G4/B1 remain complete; M2/G3 was historically unselected (open under V4.1). No unconditional proof of
  RH or target closure membership is claimed.
- Audit `AUDIT-20260715-M2-G3-02` inspected Carvill arXiv `2510.18132`, which claims
  arbitrary-order polynomial Gram decay for a smoothed dyadic-triadic BN ladder.
- The proof converts actual oscillation frequency to Manhattan distance via
  `|(j'-j)log 2+(k'-k)log 3| >= min(log 2,log 3)*(|j-j'|+|k-k'|)`.
- `LeanLab/Riemann/M2LadderFrequencyAudit.lean` checks that the admissible pair `(0,2)`, `(3,0)`
  has distance `5` and satisfies the strict reverse inequality. The proof uses exact logarithm
  monotonicity and `8<9<16`, not numerical evaluation.
- Classification is `BRANCH_FALSIFIED`, with `hard_gap_delta=0`. This rejects the published proof
  route, not necessarily every possible Gram-decay theorem, and supplies no smoothed-to-original
  closure bridge. No M2/G3 successor is admitted.
- Exact TargetChecks and transitive axiom audit pass locally with only `propext`,
  `Classical.choice`, and `Quot.sound`. The 8617-job full build, forbidden scans, and
  `git diff --check` also pass. Implementation commit
  `ff0f14f10e75d73424addb671b3da34f0c44c679` passed public Lean Action CI run `29384172003`,
  build job `87253877106`, in 2m34s. This audit batch is publicly complete.

## Previous RH handoff (2026-07-15, Wong branch falsified)

- M0, M1, G1, G2, D, and G4/B1 remain complete; M2/G3 was historically unselected (open under V4.1). No unconditional proof of
  RH or target closure membership is claimed.
- Audit `AUDIT-20260715-M2-G3-01` inspected Wong arXiv `2310.03972v5`. Its claimed
  strong-convergence route uses `norm_infinity(P_n) <= norm_2(P_n)=1` for Euclidean orthogonal
  projections.
- `LeanLab/Riemann/M2ProjectionNormAudit.lean` checks both a generic counterexample and the
  source's exact `n=3` projection. For `x=(1,1,-1,1,1)`, Lean proves `maxNorm(x)=1` and
  `maxNorm(P_3*x)=10/7`, while also checking the Gram inverse, symmetry, and idempotence of `P_3`.
- Classification is `BRANCH_FALSIFIED`, with `hard_gap_delta=0`: this rejects Wong's audited
  proof route but neither disproves RH nor supplies unconditional closure membership. No M2/G3
  successor is admitted from this source.
- Exact TargetChecks and the transitive axiom audit pass locally with only `propext`,
  `Classical.choice`, and `Quot.sound`. The 8616-job full build, forbidden scans, and
  `git diff --check` also pass. Implementation commit
  `b4894f0cb9903b5fa14c766e30bdb10c3bdeaeb4` passed public Lean Action CI run `29383306167`,
  build job `87251333374`, in 2m3s. This audit batch is publicly complete.

## Previous RH handoff (2026-07-14, G4/B1 complete)

- M0, M1, G1, G2, and D remain complete; M2/G3 was historically unselected (open under V4.1). No unconditional proof of RH or
  closure membership is claimed.
- Burnol node B1 and its fixed source frontier F0-F5 are publicly complete. F5 is implemented in
  `LeanLab/Riemann/BurnolFullLowerBound.lean`.
- Lean identifies the full constant with the half-power of the arbitrary nonnegative `ENNReal`
  zero sum, reduces it to all finite F4 bounds, and proves the exact RH-conditional continuous
  liminf endpoint without summability or countability premises.
- F0's checked distance comparison and `N -> (N : Real)^-1` convergence then give the exact
  natural endpoint `liminf d_N * sqrt(log N)` with the same full constant. This is an asymptotic
  liminf statement, not an unjustified pointwise exact-constant bound.
- Exact TargetChecks, standard-only axiom output, empty forbidden-token/declaration/resource
  scans, `git diff --check`, and the 8615-job full build pass. Implementation commit
  `9edf524877c7fcfd2112d50095eb021f3da12b0a` passed public Lean Action CI run `29352792330`,
  build job `87152928492`, in 2m23s. F5 and G4/B1 are `KNOWN_THEOREM_FORMALIZED` and complete.
- This remains formalization of Burnol's known RH-conditional obstruction, not RH or M2/G3
  progress. F0-F5 must not be reopened for standalone helper lemmas, and M2/G3 was historically unselected (open under V4.1).

## 黎曼猜想研究启动
- 2026-07-08：已按“证明工程/研究流程”启动 RH 研究；V4.1 后 RH 明确为直接目标。
  - 范围文档：`research/riemann_hypothesis_scope.md`。
  - 首批 Lean 脚手架：`LeanLab/Riemann/Basic.lean`，并已加入 `LeanLab.lean`。
  - attempts 日志：`attempts/riemann_hypothesis_initial.md`。
  - 已验证：`lake env lean LeanLab/Riemann/Basic.lean` 通过；`lake build` 通过；项目内占位证明关键字扫描无匹配。
  - 当前 Lean 小结论包括：非平凡零点谓词、临界线谓词、任意 zeta 零点满足 `Re(s) < 1`、RH 与“所有项目定义的非平凡零点在临界线上”等价、零点集合闭且离散。
  - Loop 01：新增 `RiemannHypothesis.nontrivial_zero_inCriticalStrip`，即在 RH 假设下，项目定义的非平凡零点属于开临界带；单文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 02：新增 `trivial_zero_re_lt_zero`，即标准平凡零点位置 `-2 * (n + 1)` 的实部严格小于 0；单文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 03：新增 `trivial_zero_not_inCriticalStrip`，即标准平凡零点位置不在开临界带内；单文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 04：新增 `LeanLab/Riemann/LiScaffold.lean`；本地定义 `riemannXi` 并证明 `riemannXi_one_sub`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 05：新增 `differentiable_riemannXi`；本地 `riemannXi` 全局可微；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 06：新增 `liCoefficientCandidate` 与 `liCoefficientCandidate_zero`；这只是 Li 系数候选表达式和 `n = 0` 的定义化简；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 07：新增 `riemannXi_one` 与 `riemannXi_one_ne_zero`；证明 `riemannXi 1 = 1 / 2` 且非零；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 08：新增 `riemannXi_one_mem_slitPlane`、`analyticAt_riemannXi`、`analyticAt_log_riemannXi_one`；证明 `log ∘ riemannXi` 在 `1` 处解析；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 09：新增 `differentiableAt_log_riemannXi_one`、`hasDerivAt_log_riemannXi_one`、`deriv_log_riemannXi_one`、`liCoefficientCandidate_zero_eq_logDeriv`；证明第一个 Li 候选系数等于 `deriv riemannXi 1 / riemannXi 1`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 10：新增 `deriv_riemannXi_factor_one`、`deriv_riemannXi_one`、`liCoefficientCandidate_zero_eq_completedZeta₀`；证明第一个 Li 候选系数等于 `completedRiemannZeta₀ 1`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 11：引入 `Mathlib.NumberTheory.Harmonic.ZetaAsymp`，新增 `liCoefficientCandidate_zero_eq_eulerMascheroni`；证明第一个 Li 候选系数等于 `((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 12：新增 `liCoefficientCandidate_zero_eq_ofReal`；证明第一个 Li 候选系数等于实数 `((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ)` 在 `ℂ` 中的嵌入；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 13：新增 `liCoefficientCandidate_zero_real_pos` 与 `liCoefficientCandidate_zero_re_pos`；证明第一个 Li 候选系数的实部严格为正；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 14：新增 `liCoefficientCandidate_one_eq_secondDeriv`、`deriv_id_mul_log_riemannXi_one`、`deriv_id_mul_log_riemannXi_one_eq_completedZeta₀`；建立第二个 Li 候选项的一阶导数脚手架；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 15：新增 `analyticAt_id_mul_log_riemannXi_one`、`analyticAt_deriv_id_mul_log_riemannXi_one`、`differentiableAt_deriv_id_mul_log_riemannXi_one`、`hasDerivAt_deriv_id_mul_log_riemannXi_one`；证明第二个 Li 候选项有解析可微性接口；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 16：新增 `eventually_deriv_id_mul_log_riemannXi_eq`、`liCoefficientCandidate_one_eq_deriv_productRule`；证明第二个 Li 候选项可改写为局部乘积法则展开式在 `1` 处的导数；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 17：新增 `eventually_riemannXi_mem_slitPlane_one`、`eventually_deriv_log_riemannXi_eq_logDeriv`、`eventually_deriv_log_riemannXi_eq`、`liCoefficientCandidate_one_eq_deriv_logDeriv_fraction` 等；证明第二个 Li 候选项可改写为 `log ξ + s * ξ'/ξ` 在 `1` 处的导数；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 18：新增 `deriv_riemannXi_factor`、`deriv_riemannXi`、`logDeriv_riemannXi_eq`、`liCoefficientCandidate_one_eq_deriv_expandedLogDeriv`；证明 `ξ'` 可展开为 `completedRiemannZeta₀` 及其导数的组合，并把第二个 Li 候选项改写到这个展开式；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 19：新增 `differentiableAt_logDeriv_riemannXi_one`、`deriv_id_mul_logDeriv_riemannXi_one`、`liCoefficientCandidate_one_eq_two_logDeriv_add_deriv_logDeriv`；证明 `ξ'/ξ` 在 `1` 处可微，并把第二个 Li 候选项改写为 `L(1) + (L(1) + L'(1))`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 20：新增 `logDeriv_riemannXi_one_eq_liCoefficientCandidate_zero`、`liCoefficientCandidate_one_eq_zero_add_deriv_logDeriv`；证明 `L(1)` 等于第一个 Li 候选项，并把第二个 Li 候选项改写为 `λ₀ + (λ₀ + L'(1))`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 21：新增 `deriv_logDeriv_riemannXi_one`、`liCoefficientCandidate_one_eq_zero_add_logDeriv_quotient`、`deriv_logDeriv_riemannXi_one_eq_secondDeriv`、`liCoefficientCandidate_one_eq_zero_add_secondDeriv`；用商法则把 `L'(1)` 拆到 `ξ''(1)`、`ξ'(1)`、`ξ(1)`，并用 `ξ(1)=1/2`、`ξ'(1)=completedRiemannZeta₀ 1/2` 化简；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 22：新增 `analyticAt_deriv_completedRiemannZeta₀_one`、`differentiableAt_deriv_completedRiemannZeta₀_one`、`deriv_deriv_riemannXi_one`、`liCoefficientCandidate_one_eq_completedZeta₀_deriv`；从 `ξ'` 的展开式推出 `ξ''(1) = completedRiemannZeta₀ 1 + deriv completedRiemannZeta₀ 1`，并化简 `λ₁ = 4 * completedRiemannZeta₀ 1 + 2 * deriv completedRiemannZeta₀ 1 - completedRiemannZeta₀ 1 ^ 2`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 23：新增 `deriv_completedRiemannZeta₀_one_eq_neg_zero`、`liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero`、`liCoefficientCandidate_one_eq_eulerMascheroni_neg_deriv_zero`；用 `completedRiemannZeta₀_one_sub` 把剩余导数从 `1` 点移到 `0` 点，并把 `λ₁` 写成只剩 `deriv completedRiemannZeta₀ 0` 的形式；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 24：新增 `deriv_riemannZeta_zero_numerator`；证明 `ζ'(0)` 的 completed-zeta 表达式中，分子 `(s * completedRiemannZeta₀ s - 1) - s / (1 - s)` 在 `0` 点的导数为 `completedRiemannZeta₀ 0 - 1`，所以一阶分子侧不会暴露 `deriv completedRiemannZeta₀ 0`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 25：新增 `completedRiemannZeta₀_zero_eq_one`、`liCoefficientCandidate_zero_eq_completedZeta₀_zero`、`liCoefficientCandidate_one_eq_completedZeta₀_zero_neg_deriv_zero`、`liCoefficientCandidate_one_eq_zero_neg_deriv_zero`、`liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero`；把第二个本地 Li 候选项压缩为 `λ₁ = λ₀ * (4 - λ₀) - 2 * deriv completedRiemannZeta₀ 0`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 26：新增 `liCoefficientCandidate_zero_im_eq_zero`、`liCoefficientCandidate_one_im_eq_neg_two_deriv_completedZeta₀_zero_im`、`liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re`；把 `λ₁` 的虚部化为 `-2 * (deriv completedRiemannZeta₀ 0).im`，实部化为 `λ₀.re * (4 - λ₀.re) - 2 * (deriv completedRiemannZeta₀ 0).re`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 27：引入 `Mathlib.Analysis.Calculus.Deriv.Star`，新增 `deriv_zero_im_eq_zero_of_conj_conj_eq_self`、`deriv_completedRiemannZeta₀_zero_im_eq_zero_of_conj_conj`、`liCoefficientCandidate_one_im_eq_zero_of_completedZeta₀_conj_conj`；证明函数级共轭兼容性会推出 `deriv completedRiemannZeta₀ 0` 的虚部为零，进而推出 `λ₁` 虚部为零；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 28：新增 `mellin_conj_of_forall_mem_Ioi`、`hurwitzEvenFEPair_zero_f_modif_conj`、`hurwitzEvenFEPair_zero_Λ₀_conj`、`completedRiemannZeta₀_conj`、`completedRiemannZeta₀_conj_conj`、`deriv_completedRiemannZeta₀_zero_im_eq_zero`、`liCoefficientCandidate_one_im_eq_zero`；从 Mellin 变换和 real-valued Hurwitz kernel 结构证明 `completedRiemannZeta₀` 的共轭兼容性，并推出第二个本地 Li 候选项虚部为零；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 29：新增 `deriv_completedRiemannZeta₀_zero_eq_ofReal_re`、`liCoefficientCandidate_one_eq_ofReal_re`、`liCoefficientCandidate_one_eq_ofReal_re_formula`、`liCoefficientCandidate_one_re_pos_iff_re_formula`；把第二个本地 Li 候选项写成实数嵌入的显式表达式，并把其正实部目标改写为纯实数不等式；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 30：新增 `deriv_eq_zero_at_half_of_one_sub_eq_self`、`deriv_riemannXi_half_eq_zero`、`deriv_completedRiemannZeta₀_half_eq_zero`；从 `f (1 - s) = f s` 的中心对称性推出 `1 / 2` 处导数为零，并专门化到本地 `riemannXi` 与 `completedRiemannZeta₀`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 31：新增 `half_sub_eq_of_one_sub_eq_self`、`centered_even_of_one_sub_eq_self`、`riemannXi_half_sub`、`centered_riemannXi_even`、`completedRiemannZeta₀_half_sub`、`centered_completedRiemannZeta₀_even`、`deriv_centered_zero_of_one_sub_eq_self`、`deriv_centered_riemannXi_zero`、`deriv_centered_completedRiemannZeta₀_zero`；把 `s ↦ 1 - s` 对称性改写为中心化偶性，并证明中心化函数在 `0` 处一阶导数为零；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 32：新增 `iteratedDeriv_odd_eq_zero_of_even`、`iteratedDeriv_centered_odd_eq_zero_of_one_sub_eq_self`、`iteratedDeriv_centered_riemannXi_odd_eq_zero`、`iteratedDeriv_centered_completedRiemannZeta₀_odd_eq_zero`；证明偶函数所有奇数阶 `iteratedDeriv` 在中心为零，并专门化到本地 `riemannXi` 与 `completedRiemannZeta₀` 的中心化函数；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 33：新增 `iteratedDeriv_centered_eq`、`iteratedDeriv_centered_riemannXi_eq`、`iteratedDeriv_centered_completedRiemannZeta₀_eq`、两个中心化二阶导数等于原二阶导数的版本、`analyticAt_deriv_completedRiemannZeta₀_half`、`differentiableAt_deriv_completedRiemannZeta₀_half`、`deriv_deriv_riemannXi_half`、`iteratedDeriv_centered_riemannXi_two_eq_completedZeta₀_half`；证明中心化 `riemannXi` 的二阶导数等于 `completedRiemannZeta₀ (1 / 2) - (1 / 8) * deriv (deriv completedRiemannZeta₀) (1 / 2)`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 34：新增 `value_im_eq_zero_of_conj_conj_eq_self_at_fixed`、`deriv_conj_conj_eq_self`、`complex_half_star`、`deriv_completedRiemannZeta₀_conj_conj`、`deriv_deriv_completedRiemannZeta₀_conj_conj`、`completedRiemannZeta₀_half_im_eq_zero`、`deriv_deriv_completedRiemannZeta₀_half_im_eq_zero`、两个实数嵌入版本、`iteratedDeriv_centered_riemannXi_two_im_eq_zero`、`iteratedDeriv_centered_riemannXi_two_eq_ofReal_re`；证明 `completedRiemannZeta₀ (1 / 2)`、`deriv (deriv completedRiemannZeta₀) (1 / 2)` 和中心化 `riemannXi` 二阶导数均为实值；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 35：新增 `iteratedDeriv_centered_riemannXi_two_re_eq_completedZeta₀_half_re`、`iteratedDeriv_centered_riemannXi_two_eq_ofReal_re_formula`、`iteratedDeriv_centered_riemannXi_two_re_pos_iff`；把中心化 `riemannXi` 二阶导数的正实部目标化为纯实数不等式 `(completedRiemannZeta₀ (1 / 2)).re - (1 / 8) * (deriv (deriv completedRiemannZeta₀) (1 / 2)).re > 0`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 36：新增 `riemannXi_half`、`iteratedDeriv_centered_riemannXi_zero_eq_half`、`iteratedDeriv_centered_riemannXi_zero_eq_completedZeta₀_half`、`riemannXi_half_im_eq_zero`、`riemannXi_half_eq_ofReal_re`、`riemannXi_half_re_eq_completedZeta₀_half_re`、`riemannXi_half_eq_ofReal_re_formula`、`riemannXi_half_re_pos_iff`；证明中心化 `riemannXi` 零阶项为 `1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2)`，并把其正实部目标化为纯实数不等式；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 37：新增 `completedRiemannZeta₀_half_eq_riemannXi_half`、`completedRiemannZeta₀_half_re_eq_riemannXi_half_re`、`riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four`、`iteratedDeriv_centered_riemannXi_zero_re_pos_iff_completedZeta₀_half_re_lt_four`；把中心值正性目标等价为 completed-zeta 中心值上界 `(completedRiemannZeta₀ (1 / 2)).re < 4`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 38：新增 `completedRiemannZeta₀_half_eq_hurwitzEvenFEPair_Λ₀`、`completedRiemannZeta₀_half_eq_mellin_hurwitzEvenFEPair_zero`、两个实部版本、`riemannXi_half_re_pos_iff_hurwitzEvenFEPair_Λ₀_re_lt_eight`、`riemannXi_half_re_pos_iff_mellin_hurwitzEvenFEPair_zero_re_lt_eight`；把中心值正性目标继续等价为 Mellin 侧上界 `(mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < 8`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 39：新增零参数 modified kernel 的分段公式、两侧正项级数表达，以及 `hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos`；证明对所有 `0 < x`，`0 ≤ ((hurwitzEvenFEPair 0).f_modif x).re`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 40：新增 `ofReal_cpow_quarter_sub_one`、Mellin `1 / 4` integrand 实部公式、integrand 非负性、`mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral`、`mellin_hurwitzEvenFEPair_zero_quarter_re_nonneg`、`hurwitzEvenFEPair_zero_Λ₀_quarter_re_nonneg`、`completedRiemannZeta₀_half_re_nonneg`、`riemannXi_half_re_le_one_half`；证明中心值路线中的 Mellin 实部是非负实积分，并得到 `(completedRiemannZeta₀ (1 / 2)).re ≥ 0`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 41：新增大端 `1 < x` 和小端 `0 < x < 1` 的 theta-tail 比较上界，包括 `mellin_quarter_integrand_re_le_exp_tail_of_one_lt` 与 `mellin_quarter_integrand_re_le_exp_tail_of_pos_lt_one`；证明 Loop 40 的非负 integrand 在两段上分别可由显式几何型 theta-tail 表达式控制；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 42：新增 `mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral_split`、`mellin_quarter_integral_Ioo_zero_one_nonneg`、`mellin_quarter_integral_Ioi_one_nonneg`；把 Loop 40 的 Mellin 实部积分拆成 `(0,1)` 与 `(1,∞)` 两段，并证明两段贡献均非负；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 43：新增 `mellin_quarter_integral_Ioo_zero_one_le_exp_tail` 与 `mellin_quarter_integral_Ioi_one_le_exp_tail`；在显式 majorant 可积的前提下，把 Loop 41 的点态比较提升为两段积分比较；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 44：新增 `one_sub_rexp_neg_pi_mul_pos_of_pos`、`one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_of_one_le`、`rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le`、`mellin_quarter_right_exp_tail_le_const_mul_rexp`；证明大端显式 majorant 在 `x ≥ 1` 上由常数倍 `exp (-π*x)` 点态支配；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 45：引入 `Mathlib.MeasureTheory.Integral.ExpDecay`，新增 `integrableOn_mellin_quarter_right_exp_tail`；用 Loop 44 的点态指数支配和 `integrable_of_isBigO_exp_neg` 证明大端显式 majorant 在 `Ioi 1` 上可积；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 46：新增 `mellin_quarter_integral_Ioi_one_le_integral_exp_tail`；把 Loop 43 的右段条件式积分比较用 Loop 45 的可积性实例化为无条件右段积分上界；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 47：新增 `one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_inv_of_pos_le_one`、`rexp_neg_pi_mul_inv_div_one_sub_le_const_mul_rexp_neg_pi_mul_inv_of_pos_le_one`、`mellin_quarter_left_exp_tail_le_const_mul_rexp_inv`；证明小端显式 majorant 在 `0 < x ≤ 1` 上由常数倍 `x^(-5/4) * exp (-π/x)` 点态支配；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 48：引入 `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`，新增 `integrableOn_mellin_quarter_left_near_zero_bound`；用 `u = 1/x` 的 rpow 换元和标准指数衰减积分证明 `x^(-5/4) * exp (-π/x)` 在 `(0,1)` 上可积；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 49：新增 `integrableOn_mellin_quarter_left_exp_tail`；用 Loop 47 的点态支配和 Loop 48 的近零支配函数可积性证明小端原始显式 majorant 在 `Ioo 0 1` 上可积；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 50：新增 `mellin_quarter_integral_Ioo_zero_one_le_integral_exp_tail`；把 Loop 43 的左段条件式积分比较用 Loop 49 的可积性实例化为无条件左段积分上界；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 51：新增 `mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_exp_tails`；把 Loop 42 的 Mellin 拆分等式与 Loop 50/46 的左右段比较合并，得到 Mellin 实部由两段显式 majorant 积分之和控制；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 52：新增 `mellin_quarter_left_exp_tail_integral_le_const_integral_rexp_inv`、`mellin_quarter_right_exp_tail_integral_le_const_integral_rexp`、`mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_const_exp_bounds`；把全局 majorant 上界进一步压到两个常数倍指数积分：小端 `x^(-5/4) * exp (-π/x)` 和大端 `exp (-π*x)`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 53：新增 `integral_Ioi_near_zero_bound_eq_integral_exp_tail`；用 mathlib 的 `integral_comp_rpow_Ioi` 在整个 `Ioi 0` 上形式化 `u = 1/x` 换元，把 `x^(-5/4) * exp (-π/x)` 积分改写为 `u^(-3/4) * exp (-π*u)` 积分；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 54：新增 `integrableOn_mellin_quarter_left_near_zero_bound_Ioi`、`integral_Ioo_near_zero_bound_le_integral_Ioi_near_zero_bound`、`integral_Ioo_near_zero_bound_le_integral_exp_tail_Ioi`；把小端 `(0,1)` 近零模型积分粗略放大到全半线标准尾积分 `∫ u in Ioi 0, u^(-3/4) * exp (-π*u)`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 55：新增 `integral_Ioi_one_rexp_neg_pi_mul_eq` 与 `integral_Ioi_one_const_mul_rexp_neg_pi_mul_eq`；用 `integral_exp_mul_Ioi` 精确计算大端简化指数尾积分 `∫ x in Ioi 1, exp (-π*x) = exp (-π)/π` 及其常数倍版本；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 56：新增 `integral_Ioi_exp_tail_eq_gamma_quarter` 与 `integral_Ioi_const_mul_exp_tail_eq_gamma_quarter`；用 `Real.integral_rpow_mul_exp_neg_mul_Ioi` 把小端粗上界中的全半线尾积分表示为 `(1/π)^(1/4) * Real.Gamma (1/4)` 及其常数倍版本；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 57：新增 `integral_Ioo_const_near_zero_bound_le_gamma_quarter` 与 `mellin_hurwitzEvenFEPair_zero_quarter_re_le_gamma_exp_bound`；把 Loop 52/54/55/56 合并，得到 Mellin 实部由 `2*(1-exp(-π))⁻¹ * ((1/π)^(1/4)*Real.Gamma(1/4)) + 2*(1-exp(-π))⁻¹*(exp(-π)/π)` 控制；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 58：新增 `Real.gamma_five_quarter_le_one` 与 `Real.gamma_one_quarter_le_four`；用 `Real.convexOn_Gamma` 在 `[1,2]` 上的凸性和 `Real.Gamma_add_one` 得到粗界 `Real.Gamma (1/4) ≤ 4`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 59：新增 `Real.one_div_pi_rpow_quarter_le_four_fifths`；用 `Real.pi_gt_three` 与四次方/rpow 单调性证明 `(1/π)^(1/4) ≤ 4/5`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 60：新增 `Real.rexp_neg_pi_lt_one_twentieth`；用 `Real.exp_one_gt_d9` 证明 `20 < exp 3`，再由倒数和 `Real.pi_gt_three` 推出 `exp(-π) < 1/20`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 61：新增 `Real.rexp_neg_pi_div_pi_lt_one_twentieth`；由 `π > 1`、`exp(-π) > 0` 和 Loop 60 推出 `exp(-π)/π < 1/20`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 62：新增 `Real.two_mul_one_sub_rexp_neg_pi_inv_lt_seventeen_eighths`；由 Loop 60 推出 `1-exp(-π)>19/20`，再取倒数并乘 2 得到 `2*(1-exp(-π))⁻¹ < 17/8`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 63：新增 `mellin_gamma_exp_bound_lt_eight`；把 Loops 58/59/61/62 的有理数界合并，证明 Loop 57 的显式 Gamma/指数上界本身 `< 8`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 64：新增 `mellin_hurwitzEvenFEPair_zero_quarter_re_lt_eight`；由 Loop 57 的全局上界和 Loop 63 的显式界经传递性推出 Mellin 实部 `< 8`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 65：新增 `riemannXi_half_re_pos`；用 Loop 38 的等价定理和 Loop 64 的 Mellin 实部界推出项目本地 `riemannXi (1/2)` 的实部严格为正；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 66：新增 `riemannXi_half_mem_slitPlane`；由 Loop 65 的正实部结论推出中心值属于复对数使用的 `slitPlane`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 67：新增 `analyticAt_log_riemannXi_half`；用 `analyticAt_riemannXi` 与 Loop 66 的 slit-plane 条件证明 `log ∘ riemannXi` 在中心点解析；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 68：新增 `differentiableAt_log_riemannXi_half`、`hasDerivAt_log_riemannXi_half`、`deriv_log_riemannXi_half`、`deriv_log_riemannXi_half_eq_zero`；证明中心点 `log ∘ riemannXi` 可微、导数公式成立且一阶导数为零；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 69：按新协议消掉 Tier 1 target `T1.xi.completed.bridge`；新增 `riemannXi_eq_mul_completedRiemannZeta`，证明在 `s ≠ 0,1` 时本地 `riemannXi s = s*(s-1)/2*completedRiemannZeta s`；`Targets.lean` 已把该 target 标为 `.proven`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 70：填充 blueprint 子节点 `T1.xi.zero.bridge.forward.safe`；新增 `isZetaZero_of_riemannXi_eq_zero`，证明 `s ≠ 0,1` 且 `riemannXi s = 0` 时 `IsZetaZero s`；完整零点等价仍未完成，反方向需处理 Gamma 因子和平凡零点；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 71：填充 blueprint 子节点 `T1.xi.zero.bridge.reverse.gamma`；新增 `completedRiemannZeta_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero` 与 `riemannXi_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero`，证明 zeta 零点在 `Gammaℝ s ≠ 0` 且 `s ≠ 0,1` 条件下推出 xi 零点；完整非平凡包装仍待处理；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 72：填充 blueprint 子节点 `T1.xi.zero.bridge.gamma.edge`；新增 `eq_zero_or_isTrivialZeroPoint_of_Gammaℝ_eq_zero` 与 `Gammaℝ_ne_zero_of_isNontrivialZero`，证明 `Gammaℝ` 零点只能是 `0` 或项目平凡零点，且项目非平凡 zeta 零点排除 Gamma 因子零点；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 73：填充 blueprint 子节点 `T1.xi.zero.bridge.reverse.nontrivial`；新增 `ne_zero_of_isNontrivialZero` 与 `riemannXi_eq_zero_of_isNontrivialZero`，证明项目非平凡 zeta 零点推出本地 `riemannXi` 零点；完整桥接 theorem 尚待包装；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 74：填充并关闭 blueprint 子节点 `T1.xi.zero.bridge.nontrivial`；新增 `riemannXi_zero`、`riemannXi_zero_ne_zero`、`riemannXi_one`、`riemannXi_one_ne_zero` 与 `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial`，证明 `IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬ IsTrivialZeroPoint s`；`Targets.lean` 已把 `T1.xi.zero.bridge` 标为 `.proven`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 75：对 `T1.li1.positivity` 做有界库存并新增 reducer；新增 `liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt`、`liCoefficientCandidate_zero_re_lt_four`、`liCoefficientCandidate_zero_re_mul_four_sub_pos`，把第二个本地 Li 候选项正实部目标等价压缩为 `(deriv completedRiemannZeta₀ 0).re` 的单一上界，并证明该上界阈值的乘积项为正；库存未发现 mathlib 中该导数的直接特殊值，`ζ'(0)` 一阶路线被记录为不暴露该导数；`Targets.lean` 已把 `T1.li1.positivity` 标为 `.inProgress`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 76：填充 blueprint 子节点 `T1.li1.mellin.deriv.reduction`；新增 `deriv_completedRiemannZeta₀_zero_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero`、其实部版本，以及 `liCoefficientCandidate_one_re_pos_iff_deriv_hurwitzEvenFEPair_Λ₀_zero_re_lt`，把第二个本地 Li 候选项正实部目标进一步等价为 `(deriv (hurwitzEvenFEPair 0).Λ₀ 0).re < 2*((λ₀.re)*(4-λ₀.re))`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 77：填充 blueprint 子节点 `T1.li1.mellin.log.deriv` 与 `T1.li1.mellin.log.bound.reduction`；新增 `mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero`、`deriv_hurwitzEvenFEPair_Λ₀_zero_eq_mellin_log_f_modif_zero`、`liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt`，用 mathlib 的 `mellin_hasDerivAt_of_isBigO_rpow` 把第二个本地 Li 候选项正实部目标等价为 log-weighted Mellin 积分实部上界；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 78：填充 blueprint 子节点 `T1.li1.mellin.log.integral.split`；新增 `ofReal_cpow_zero_sub_one`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real`，把 log-weighted Mellin 项拆成 `(0,1)` 与 `(1,∞)` 两段实积分，integrand 为 `x^(-1)*Real.log x*((hurwitzEvenFEPair 0).f_modif x).re`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 79：填充 blueprint 子节点 `T1.li1.mellin.log.left.nonpos`；新增 `mellin_log_integral_Ioo_zero_one_nonpos` 与 `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one`，利用 `(0,1)` 上 `Real.log x ≤ 0` 和 modified kernel 实部非负，证明小端贡献非正，并把剩余上界问题压到 `(1,∞)` 右段积分；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 80：填充 blueprint 子节点 `T1.li1.mellin.log.right.exp_tail`；新增 `mellin_log_right_integrand_re_le_exp_tail_of_one_lt` 与条件式积分比较 `mellin_log_integral_Ioi_one_le_exp_tail`，把右段积分压到 `x^(-1)*Real.log x*(2*(exp(-π*x)/(1-exp(-π*x))))` 的 log-weighted 指数尾 majorant；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 81：填充 blueprint 子节点 `T1.li1.mellin.log.right.exp_tail.integrable`；新增 `mellin_log_right_exp_tail_le_const_mul_rexp` 与 `integrableOn_mellin_log_right_exp_tail`，用 `log x / x ≤ 1` 和旧的分母比较把 log-weighted 指数尾 majorant 压到常数倍 `exp(-π*x)`，并由指数衰减定理证明其在 `Ioi 1` 上可积；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 82：填充 blueprint 子节点 `T1.li1.mellin.log.right.exp_tail.closed_bound`；新增 `mellin_log_integral_Ioi_one_le_integral_exp_tail`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_exp_tail`、`mellin_log_right_exp_tail_integral_le_const_integral_rexp`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_const_exp`、`mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound`，把 log-weighted Mellin 实部上界压到显式常数 `(2*(1-exp(-π))⁻¹)*(exp(-π)/π)`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 83：填充 blueprint 子节点 `T1.li1.mellin.log.right.exp_tail.rational_bound`；新增 `mellin_log_const_exp_bound_lt_seventeen_over_one_sixty` 与 `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`，用 Loops 61-62 的数值界把 log-weighted Mellin 实部上界进一步压到 `< 17/160`；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 84：填充 blueprint 子节点 `T1.li1.threshold.rational_lower` 并关闭 `T1.li1.positivity`；新增 `Real.eulerMascheroniConstant_gt_571_over_1000`、`Real.log_four_mul_pi_lt_2533_over_1000`、`liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty`、`liCoefficientCandidate_zero_re_lt_one`、`liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`、`liCoefficientCandidate_one_re_pos`，证明第二个本地 Li 候选项实部为正；新文件验证、全项目构建和占位关键字扫描均通过。
  - Loop 85：关闭文档目标 `T1.note.li.scaffold`；新增 `research/li_scaffold_note_20260709.md`，列出已编译的本地 xi bridge、zero bridge、center scaffold、前两个本地 Li 候选正性结果，并明确不声称 Li 判据、所有系数正性或 RH；目标账本验证、全项目构建和占位关键字扫描均通过。
  - Loop 86：关闭库存目标 `T2.inventory.li.hadamard`；新增 `research/tier2_li_hadamard_inventory_20260709.md`，确认 mathlib 有局部解析、divisor、Jensen/log-counting、zeta-zero-set 与 log-derivative 支持，但缺直接 Li 判据、全局 xi Hadamard 乘积、带重数零点枚举、系数到零点和桥；结论是不把 Li/Hadamard 作为立即 Tier 2 路线，先盘点 Nyman-Beurling/Báez-Duarte；目标账本验证、全项目构建和占位关键字扫描均通过。
  - Loop 87：关闭库存目标 `T2.inventory.nyman.beurling`；新增 `research/tier2_nyman_beurling_inventory_20260709.md`，确认 mathlib 有 `L2`/Hilbert 内积、indicator-in-`Lp`、simple-function dense、区间有限测度、`Int.fract`/measurability、Hilbert subspace closure/orthogonality 支持；没有现成 Nyman-Beurling 或 Baez-Duarte criterion；建议下一步 `T2.pivot` 选择 Nyman-Beurling foundation route；目标账本验证、全项目构建和占位关键字扫描均通过。
  - Loop 88：关闭 `T2.pivot` 并选择 Nyman-Beurling foundation route；新增 `LeanLab/Riemann/NymanBeurling.lean`，定义 `fractionalPartKernel a x = Int.fract (a / x)`，证明其可测、位于 `[0,1)`、范数至多 `1`，并证明 `fractionalPartKernel_memLp_two_unitInterval`，把每个 kernel 包装成 `fractionalPartKernelL2 : Lp ℝ 2 (volume.restrict (Set.Ioo 0 1))`；`Targets.lean` 已新增下一节点 `T2.nyman.span.scaffold`；新文件验证和全项目构建通过。
  - Loop 89：关闭 `T2.nyman.span.scaffold`；在 `LeanLab/Riemann/NymanBeurling.lean` 中新增 `unitIntervalL2`、`nymanBeurlingKernelSpan`，并证明 `fractionalPartKernelL2_mem_nymanBeurlingKernelSpan`、`range_fractionalPartKernelL2_subset_nymanBeurlingKernelSpan`、`nymanBeurlingKernelSpan_le`；`Targets.lean` 已新增下一节点 `T2.nyman.closure.scaffold`。
  - Loop 90：关闭 `T2.nyman.closure.scaffold`；新增 `nymanBeurlingKernelClosure`，证明 `nymanBeurlingKernelSpan_le_closure`、`isClosed_nymanBeurlingKernelClosure`、`nymanBeurlingKernelClosure_coe`、`fractionalPartKernelL2_mem_nymanBeurlingKernelClosure`；`Targets.lean` 已新增下一节点 `T2.nyman.density.predicate`。
  - Loop 91：关闭 `T2.nyman.density.predicate`；新增 `nymanBeurlingKernelDense`，证明 `nymanBeurlingKernelDense_iff_closure_eq_top` 与 `nymanBeurlingKernelDense_iff_forall_mem_closure`；`Targets.lean` 已新增下一节点 `T2.nyman.orthogonal.reformulation`。
  - Loop 92：关闭 `T2.nyman.orthogonal.reformulation`；新增 `nymanBeurlingKernelDense_iff_orthogonal_eq_bot`，证明 kernel-span 密度等价于其正交补为底；`Targets.lean` 已新增下一节点 `T2.nyman.orthogonal.pointwise`。
  - Loop 93：关闭 `T2.nyman.orthogonal.pointwise`；新增 `mem_nymanBeurlingKernelSpan_orthogonal_iff`，把正交补成员条件展开为对所有 packaged fractional-part kernel 的内积为零；`Targets.lean` 已新增下一节点 `T2.nyman.density.pointwise`。
  - Loop 94：关闭 `T2.nyman.density.pointwise`；新增 `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`，把密度等价为所有对 packaged kernels 内积为零的 `L²` 向量都为零；`Targets.lean` 已新增下一节点 `T2.nyman.inner.integral.inventory`。
  - Loop 95：关闭 `T2.nyman.inner.integral.inventory`；新增 `research/tier2_nyman_inner_integral_inventory_20260710.md` 与 `inner_fractionalPartKernelL2_eq_integral`，把 packaged kernel 的内积改写成受限单位区间上的积分；`Targets.lean` 已新增下一节点 `T2.nyman.density.integral`。
  - Loop 96：关闭 `T2.nyman.density.integral`；新增 `nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero`，把密度障碍命题整体改写成对 concrete fractional-part kernels 的积分消失条件；`Targets.lean` 已新增下一节点 `T2.nyman.constant.one.l2`。
  - Loop 97：关闭 `T2.nyman.constant.one.l2`；新增 `unitIntervalOne`、`unitIntervalOne_memLp_two_unitInterval`、`unitIntervalOneL2`、`unitIntervalOneL2_coeFn`、`unitIntervalOneL2_coeFn_const`，把常数一函数包装成 `unitIntervalL2` 中的目标向量；`Targets.lean` 已新增下一节点 `T2.nyman.density.one.closure`。
  - Loop 98：关闭 `T2.nyman.density.one.closure`；新增 `unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense`，在条件 `nymanBeurlingKernelDense` 下推出常数一目标向量属于 `nymanBeurlingKernelClosure`；`Targets.lean` 已新增下一节点 `T2.nyman.one.closure.epsilon`。
  - Loop 99：关闭 `T2.nyman.one.closure.epsilon`；新增 `unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt` 与 `exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense`，把常数一闭包成员关系改写为由 `nymanBeurlingKernelSpan` 中元素进行 epsilon 距离近似的形式；`Targets.lean` 已新增下一节点 `T2.nyman.span.finite.approx`。
  - Loop 100：关闭 `T2.nyman.span.finite.approx`；新增 `mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum`、`unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt`、`exists_finsupp_sum_fractionalPartKernelL2_dist_unitIntervalOneL2_lt_of_dense`，把 span 近似元展开为 packaged fractional-part kernels 的有限实线性组合；`Targets.lean` 已新增下一节点 `T2.nyman.finite.approx.norm`。
  - Loop 101：关闭 `T2.nyman.finite.approx.norm`；新增 `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt` 与 `exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`，把有限组合近似从距离形式改写成差的范数形式；`Targets.lean` 已新增下一节点 `T2.nyman.finite.approx.integral.inventory`。
  - Loop 102：关闭 `T2.nyman.finite.approx.integral.inventory`；新增库存文档 `research/tier2_nyman_finite_approx_integral_inventory_20260710.md`，并证明 `unitIntervalL2_norm_sq_eq_integral_mul_self` 与 `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self`，把 `unitIntervalL2` 范数平方改写成代表函数自乘积分；`Targets.lean` 已新增下一节点 `T2.nyman.finite.approx.representatives`。
  - Loop 103：关闭 `T2.nyman.finite.approx.representatives`；新增 `finsupp_sum_fractionalPartKernelL2_coeFn`、`unitIntervalOneL2_sub_finsupp_sum_fractionalPartKernelL2_coeFn` 与 `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete`，把有限 packaged kernel 组合及常数一差的代表元识别为具体 fractional-part 有限和，并把范数平方积分改写成 concrete squared-error 积分；`Targets.lean` 已新增下一节点 `T2.nyman.finite.approx.integral.epsilon`。
  - Loop 104：关闭 `T2.nyman.finite.approx.integral.epsilon`；新增 `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense`，在 `nymanBeurlingKernelDense` 和 `0 < ε` 下给出有限系数，使 concrete squared-error 积分小于 `ε ^ 2`；`Targets.lean` 已新增下一节点 `T2.nyman.finite.approx.integral.tolerance`。
  - Loop 105：关闭 `T2.nyman.finite.approx.integral.tolerance`；新增 `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance`，用 `Real.sqrt δ` 把 `ε ^ 2` 界改成任意正容差 `δ`；`Targets.lean` 已新增下一节点 `T2.nyman.concrete.approx.predicate`。
  - Loop 106：关闭 `T2.nyman.concrete.approx.predicate`；新增 `nymanBeurlingConcreteApprox` 与 `nymanBeurlingConcreteApprox_of_dense`，把 concrete finite-approximation 性质包装成项目内短谓词，并证明 `nymanBeurlingKernelDense` 推出该性质；`Targets.lean` 已新增下一节点 `T2.nyman.classical.criterion.inventory`。
  - Loop 107：关闭 `T2.nyman.classical.criterion.inventory`；新增 `research/tier2_nyman_classical_criterion_inventory_20260710.md`，记录当前谓词与经典 Nyman-Beurling/Baez-Duarte 形状之间的参数域、自然参数、定义域/目标函数、closure/tolerance、criterion-to-RH 五类差距；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.concrete.approx.predicate`。
  - Loop 108：关闭 `T2.nyman.restricted.concrete.approx.predicate`；新增 `nymanBeurlingRestrictedConcreteApprox` 与 `nymanBeurlingConcreteApprox_of_restricted`，把有限系数支撑限制在 `0 < a ∧ a ≤ 1` 的 concrete approximation 谓词正式包装，并证明它推出 unrestricted 谓词；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.span.scaffold`。
  - Loop 109：关闭 `T2.nyman.restricted.span.scaffold`；新增 restricted parameter/kernel set 与 `nymanBeurlingRestrictedKernelSpan`，证明 restricted generator membership 和 `nymanBeurlingRestrictedKernelSpan_le`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.closure.scaffold`。
  - Loop 110：关闭 `T2.nyman.restricted.closure.scaffold`；新增 `nymanBeurlingRestrictedKernelClosure`、span-to-closure、closedness、closure coercion、`nymanBeurlingRestrictedKernelClosure_le` 以及 restricted generator-to-closure theorem；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.density.predicate`。
  - Loop 111：关闭 `T2.nyman.restricted.density.predicate`；新增 `nymanBeurlingRestrictedKernelDense` 及 closure-top / pointwise-closure 两个等价形式；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.density.implies.unrestricted`。
  - Loop 112：关闭 `T2.nyman.restricted.density.implies.unrestricted`；新增 `nymanBeurlingKernelDense_of_restricted`，用 restricted closure 到 unrestricted closure 的包含关系证明 restricted density 推出 unrestricted density；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.density.concrete.approx`。
  - Loop 113：关闭 `T2.nyman.restricted.density.concrete.approx`；新增 `nymanBeurlingConcreteApprox_of_restrictedKernelDense`，组合 restricted density 到 unrestricted density 的桥与 `nymanBeurlingConcreteApprox_of_dense`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.density.one.closure`。
  - Loop 114：关闭 `T2.nyman.restricted.density.one.closure`；新增 `unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense`，把 restricted density 实例化到常数一目标向量；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.one.closure.epsilon`。
  - Loop 115：关闭 `T2.nyman.restricted.one.closure.epsilon`；新增 restricted closure membership 的 epsilon-distance 等价与 restricted-density approximant existence 推论；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.span.finite.approx`。
  - Loop 116：关闭 `T2.nyman.restricted.span.finite.approx`；新增 `restrictedFractionalPartKernelL2`、restricted kernel set 的 range 表达，以及 restricted span membership 到 subtype-indexed `Finsupp` 有限和的等价；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.dist`。
  - Loop 117：关闭 `T2.nyman.restricted.finite.approx.dist`；新增 subtype-indexed finite-sum 距离近似定理 `exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.norm`。
  - Loop 118：关闭 `T2.nyman.restricted.finite.approx.norm`；新增 subtype-indexed finite-sum 范数近似定理 `exists_restricted_finsupp_sum_norm_sub_lt_of_dense`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.integral.inventory`。
  - Loop 119：关闭 `T2.nyman.restricted.finite.approx.integral.inventory`；新增 inventory 文档与 restricted finite-sum 范数平方积分桥 `norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.representatives`。
  - Loop 120：关闭 `T2.nyman.restricted.finite.approx.representatives`；新增 restricted finite-sum 代表元桥、常数一差代表元桥与 concrete norm-square 积分桥；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.integral.epsilon`。
  - Loop 121：关闭 `T2.nyman.restricted.finite.approx.integral.epsilon`；新增 restricted concrete squared-error 积分 `< ε ^ 2` 定理 `exists_restricted_finsupp_integral_sq_lt_of_dense`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.integral.tolerance`。
  - Loop 122：关闭 `T2.nyman.restricted.finite.approx.integral.tolerance`；新增任意正容差版本 `exists_restricted_finsupp_integral_lt_of_dense_tolerance`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.finite.approx.real.support`。
  - Loop 123：关闭 `T2.nyman.restricted.finite.approx.real.support`；新增 subtype-indexed 系数到 real-indexed support 受限系数的桥 `exists_real_finsupp_of_restricted_finsupp` 与积分存在桥 `exists_real_finsupp_integral_lt_of_restricted`；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.concrete.approx.of.dense`。
  - Loop 124：关闭 `T2.nyman.restricted.concrete.approx.of.dense`；新增 `nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense`，把 restricted density 包装成 restricted concrete approximation 谓词；`Targets.lean` 已新增下一节点 `T2.nyman.restricted.route.summary`。
  - Loop 125：关闭 `T2.nyman.restricted.route.summary`；新增 `research/tier2_nyman_restricted_route_summary_20260710.md`，总结 restricted branch 的已编译链条与剩余 classical gap；`Targets.lean` 已新增下一节点 `T2.nyman.baez.duarte.natural.index.inventory`。
  - Loop 126：关闭 `T2.nyman.baez.duarte.natural.index.inventory`；新增 `research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md`，选择 `{n : Nat // 0 < n}` 与 reciprocal map `n ↦ ((n : Real)⁻¹)` 作为自然参数桥的下一步；`Targets.lean` 已新增下一节点 `T2.nyman.baez.duarte.reciprocal.map`。
  - Loop 127：关闭 `T2.nyman.baez.duarte.reciprocal.map`；新增 `baezDuartePositiveNatIndex`、`baezDuarte_reciprocal_mem_restricted`、`baezDuarteReciprocalParameter`、`baezDuarteReciprocalEmbedding`；`Targets.lean` 已新增下一节点 `T2.nyman.baez.duarte.natural.finsupp.bridge`。
  - Loop 128：关闭 `T2.nyman.baez.duarte.natural.finsupp.bridge`；新增 `exists_restricted_finsupp_of_baezDuarte_finsupp`，用 `Finsupp.embDomain` 沿 `baezDuarteReciprocalEmbedding` 把 positive-natural 系数运输到 restricted-parameter 系数并保持 concrete reciprocal finite sum；`Targets.lean` 已新增下一节点 `T2.nyman.baez.duarte.natural.integral.bridge`。
  - Loop 129：关闭 `T2.nyman.baez.duarte.natural.integral.bridge`；新增 `exists_restricted_finsupp_integral_lt_of_baezDuarte`，把 positive-natural reciprocal squared-error integral bound 运输到 restricted-parameter integral bound；`Targets.lean` 已新增下一节点 `T2.nyman.baez.duarte.natural.concrete.approx.predicate`。
  - Loop 130：关闭 `T2.nyman.baez.duarte.natural.concrete.approx.predicate`；新增 `nymanBeurlingBaezDuarteConcreteApprox` 与 `nymanBeurlingRestrictedConcreteApprox_of_baezDuarte`，把 positive-natural reciprocal approximation predicate 连接回 restricted concrete approximation；`Targets.lean` 已新增下一节点 `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted`。

## Arch 审计第四轮（2026-07-16，Claude）：三判据齐备，外审债务=头号风险
- **验证属实**：Li 判据完整 iff（`riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg`，反向=B-L 论证）、Li-Weil Gram iff、Burnol 下界（B1/G4）、紧 C⁶ Weil 显式公式、Gaussian 族等价（W2 部分，无条件符号如实标 open）。284 条公理审计重跑零非标准信任基；全仓零 sorry 含 vendor 代码；三个 iff 签名均无隐藏假设。
- Hadamard 缺口 = vendor PNT+ 62 文件（零 sorry、署名合规）复用其分解定理——协议"盘点外部仓"的正确执行；公理审计传递覆盖。
- M2 纪律保持：Polson/Freedman/Wong/Carvill 四篇 arXiv RH 宣称经 Lean 反模型/stop audit 拒绝，均声明不影响 RH 真伪。campaign 制（prereg→CI→hard_gap_delta 结算）运转良好。
- **当时的头号问题：README 仍是模板占位符，7/13 三关（Sol review/Zulip/novelty audit）零执行，未外审 spine iff 已积到 3 个。** Exposure sprint、vendor 固定源 commit、novelty audit 和 mathlib PR 队列现已执行；V4.1 废除了外审债务配额及 W2 尝试预批准，三方签核只约束对外发布。

## Arch 审计：M1-18 / G1 关闭（2026-07-13，Claude）
- **审计结论：属实。** `riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure`（BaezDuarteForwardLimit.lean:1645）= Báez-Duarte 2002 正整数强化判据 ⟺ mathlib `RiemannHypothesis` 的完整等价。定义逐项对齐文献（χ_(0,1] / ρ(1/(nx)) n∈ℕ+ / L²(0,∞) / span 拓扑闭包）；公理审计独立复跑 31 条全部仅依赖三条标准公理；无 sorry/自定义公理/native_decide；iff 无额外假设。
- 定级：数学=已知定理；形式化=极可能任何证明助手首次（待 novelty audit），发表级。配套基建（1/ζ subpower、截断 Perron、ζ 凸性、Fourier–Mellin 等距）= mathlib 空缺。
- **发布前置条件与下一步方向：`~/Downloads/review_rh_m1_audit_20260713.md`**——Sol max 逐定理 review + Zulip 外审 + novelty audit 三关齐才可对外称"首次形式化"；新节点建议 mathlib 上游化为主线 + Burnol 下界 d_N²≳C/log N 为研究线。V4.1 后 G3 已开放为直接 loop 目标；TargetChecks iff witness、hard-gap DAG 和对外发布 gate 继续有效。

## Post-M1 治理与 P1 审查（2026-07-13）
- `AUDIT-20260713-POST-M1-01` 已给最终 iff 增加精确 `TargetChecks.lean` 类型见证，并记录 G4 Burnol 已知下界线和 P1-P3 发布门；其中 G3 自动禁入条款已被 V4.1 删除。
- P1 已由干净上下文 Sol 5.6 max 只读逐定理审查关闭：reverse、forward-limit、truncated-Perron 未发现 P0-P3 问题，决定 `CONTINUE`；记录见 `research/m1_sol_max_review_20260713.md`。P2 Zulip 外审与 P3 novelty audit 仍未完成，不得对外称“首次形式化”。
- 全项目 `lake build` 8608 jobs 通过；无 `sorry`/`admit`/`sorryAx`、无项目 `axiom`/`constant`。治理提交 `fba10e7` 通过公开 CI run `29224952001`、build job `86737084562`。本批分类 `FORMALIZATION_ONLY`，不改变 RH、M2 或 G3。

## G4-01 Burnol 下界依赖审计（2026-07-13）
- 原文主对象是连续参数复空间 `B_lambda = span{rho(theta/t) : lambda<=theta<=1}`，不是项目现有的全体正整数核闭包。对有限自然空间 `V_N`，正确包含为 `V_N <= B_(1/N)`，故距离方向为 `D(1/N) <= d_N`；因此 Burnol 下界可以向自然距离转移。
- 源证明固定拆为 F0 连续/自然陈述对齐、F1 unitary distance model、F2 Burnol 正交向量、F3 Gram/Cauchy 渐近、F4 有限零点集 liminf 下界、F5 全零点和与自然转移。详细矩阵见 `research/g4_burnol_dependency_audit_20260713.md`。
- 本轮分类 `DEPENDENCY_GAP_IDENTIFIED`，未新增 Lean 定理，不改变 M2/G3。下一批只能把 F0 的 span/distance/inclusion 一次性完成并记为 `FORMALIZATION_ONLY`；随后必须进入 F1 源级分析，禁止逐个包装距离引理刷轮次。

## G4-F0 连续/自然空间对齐（2026-07-13）
- `BurnolLowerBound.lean` 定义 Burnol 的连续参数核空间 `B_lambda`、有限自然核空间 `V_N` 及两个距离；Lean 验证 `V_N <= B_(1/N)` 与 `D(1/N) <= d_N`。
- Lean 同时验证 `1/N -> 0+`，因而后续 Burnol 的 `lambda -> 0+` liminf 结论可沿正确方向转移到自然子空间。这一批严格分类为 `FORMALIZATION_ONLY`，不改变 M2/G3。
- 当时 G4 的下一目标是 F1：源级审计并形式化 Burnol 的 unitary distance model
  `D(lambda)=dist(chi1,C_lambda)`。G3/M2 在 V4.1 下开放。
- 实现提交 `1383db8e9cea271874b7f4f399eb35d1cf07f103`；公开 GitHub Actions run `29225515844`、build job `86738660740` 成功。

## G4-F1-01 unitary distance model 审计（2026-07-13）
- 原文距离等距的精确算子是 `T=(1-M)^-1`，临界线 Mellin 乘子为 `(s-1)/s`。符号核对为 `T chi=chi1`、`T rho(1/t)=-A`；负号不改变复 span。
- 归一化伸缩为 `D_theta f(t)=theta^(-1/2)f(t/theta)`，因此项目核 `rho(theta/t)=sqrt(theta)D_theta f(t)`；这一标量不改变 span，但必须在 Lean 映射定理中显式出现。
- 审计拒绝了把 `C_lambda` 直接定义成等距像的同义反复。F1 固定拆为 F1a（显式 Burnol `A` 的支撑、`L2`、Mellin 命题）与 F1b（乘子等距、核/span/距离转移）；该历史批次选择 F1a，G3/M2 在 V4.1 下开放。
- 审计提交 `35fc37c44dd8790ec5b0d55ba4d6c166073aa59a`；公开 GitHub Actions run `29226167722`、build job `86740559793` 成功。

## G4-F1a 显式 Burnol A（2026-07-13）
- 新模块 `LeanLab/Riemann/BurnolA.lean` 直接定义原文的 floor/factorial 公式；Lean 证明
  `t>1` 时为零，并证明精确恒等式
  `A(t)=integral_(u>t) rho(1/u)/u du-rho(1/t)`。尾部 `u>1` 的积分恰为 `1`，解释并验证了
  原文公式中的常数项。
- 由 `|A(t)|<=2+|log t|` 及 `|log t|*t^(1/4)<4`，Lean 证明
  `burnolA_memLp_two_positiveHalfLine`，并构造 `burnolComplexAL2` 与代表元定理。
- 二维核显式支撑于 `0<t<u`；Lean 先证明其绝对可积，再应用 Fubini 得到 Hardy 尾算子在
  Mellin 侧乘以 `1/s`。与已编译的 `Mellin(rho(1/t))=-zeta(s)/s` 合成后，主定理
  `hasMellin_burnolA` 给出 `Mellin(A)(s)=(s-1)zeta(s)/s^2`，有效域 `0<Re(s)<1`。
- 本批分类 `KNOWN_THEOREM_FORMALIZED`：只关闭 G4/F1a；不改变 RH、M2 或 G3。下一固定目标
  是 F1b：构造临界线乘子 `(s-1)/s` 的 `L2` 等距、验证 target/kernel 映射、span 转移及
  `D(lambda)=dist(chi1,C_lambda)`。不得跳到 F2，也不得用像空间定义制造同义反复。
- 实现提交 `6800d29b2b197e8d2ae33a3c3dd6c0298a05ad73`；公开 GitHub Actions run
  `29228962278`、build job `86748844527` 成功。

## G4-F1b 酉距离模型组装（2026-07-13）
- 新模块 `LeanLab/Riemann/BurnolHardy.lean` 在频率归一化
  `s=1/2+(2*pi*xi)I` 下构造乘子 `(s-1)/s` 及其共轭逆，并证明它们给出复 `L2` 上的
  线性等距同构；经 Fourier-Mellin 共轭得到半正轴上的 `burnolHardyInverseL2`。
- `chi1(t)=(1+log t)chi_(0,1](t)` 与每个模型核 `A(t/theta)` 都是显式定义，不是等距像
  的同义定义。Lean 证明对应的 `L2` 代表元与 Mellin/Fourier 公式。
- 主映射定理精确保留源文符号：`T chi=chi1` 且对每个允许的 `theta`，
  `T rho(theta/t)=-A(t/theta)`。复 span 吸收负号后，原核 span 被精确映到显式模型 span。
- `burnolDistance_eq_modelDistance` 由上述等距和 span 等式推出 Burnol 的精确距离模型。
  本批分类 `KNOWN_THEOREM_FORMALIZED`，只关闭 G4/F1b；G4 仍进行中，下一固定目标为 F2
  的 `Y(lambda,s,k)` 存在性与正交性。M2/G3 在 V4.1 下开放。
- 全项目构建 8611 jobs、精确 target witnesses、占位/显式声明扫描、axiom audit 和
  `git diff --check` 均通过。实现提交 `087f07a28c48794d9dbfec30309759a05b37db20`；公开
  GitHub Actions run `29231279145`、build job `86755849239` 成功。

## G4-F2 Burnol 向量依赖审计（2026-07-13）
- 原文 v2 TeX 已按 SHA-256
  `8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7` 复核。F2 使用的
  `V` 不是 F1b 的距离等距 `T`，而是显式 `A` 的 Mellin 相位；其源码乘子为
  `(s/(1-s))^3*zeta(1-s)/zeta(s)`，在临界线零点处必须以全定义单位模相位处理。
- `V`、物理截断 `Q_lambda`、`psi(w,k)` 和左半平面配对只是批内 Gate A。`Y` 的边界
  `L2` 极限依赖振荡核 `phi(w,k)`：`k=0` 明确引用 BBLS Lemmas 4/6，`k>=1` 由 Burnol
  的积分与显式级数延拓处理，再经两次 Hardy 平均和支配收敛完成。
- F3 将直接使用 `V(Y)` 在 `(lambda,1]` 的有界误差和 `[1,infinity)` 上
  `(1+log t)^2/t` 的统一界。因此从正交补任取向量、只证明配对、或用未证明的 `lim`
  定义 `Y` 都不能关闭 F2。
- 审计分类 `DEPENDENCY_GAP_IDENTIFIED`，没有新增 Lean 定理或关闭 F2。下一批已固定为一个
  不可拆分的 G4/F2 实现：真实相位/截断/预极限、振荡延拓、临界线极限、代表估计、精确
  配对及解析阶正交性必须一起通过；F3 在该历史批次中未提前开始，M2/G3 在 V4.1 下开放。
- 审计提交 `6aa73266bf0697383f535358160a033e0fcd2893`；公开 Lean Action CI run
  `29232724946` 成功，build job `86760317208`。

## G4-F2 Burnol 边界向量实现（2026-07-13）
- `BurnolY.lean` 构造全定义单位模第二相位 `V`、物理时间反演与截断、`psi(w,k)`、振荡延拓
  `phi(w,k)` 及临界线边界向量 `Y(lambda,s,k)`；没有用正交补反向定义 `Y`。
- Lean 逐项关闭振荡积分、级数、Hardy 两次平均、Mellin/Fourier 相位恒等和局部统一支配，
  得到 `tendsto_burnolPreY` 的真实 `L2` 边界收敛。
- `V(Y)` 的显式代表在 `t<lambda` 为零，在 `[lambda,1]` 与主谱导数之差有与 `lambda`
  无关的常数界，在 `[1,infinity)` 有 `(1+|log t|)^2/t` 界，满足 F3 消费条件。
- `inner_burnolY_normalizedModelKernel` 给出 Burnol 直向源
  `(-1)^k d^k[theta^(s-1/2) Z(s)]`；解析阶条件经乘积导数公式推出
  `burnolY_mem_modelKernelSpan_orthogonal`，覆盖完整模型 span。
- 本批分类 `KNOWN_THEOREM_FORMALIZED`：只关闭 G4/F2 并选择 F3；F4-F5 未开始，M2/G3
  在 V4.1 下开放。本地 8612-job 全构建、精确 TargetChecks、占位/声明扫描、axiom audit 与
  `git diff --check` 通过；F2 审计面仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 实现提交 `21f600b6de9e859dc9d912a82db6411547bae325`；公开 Lean Action CI run
  `29278978470`、build job `86915163555` 成功。

## 双审计合议（2026-07-10，Claude arch × GPT-5.6 Sol）
- Sol 独立审计结论与 arch 7/09 审查一致：**合格的 RH 周边形式化工程，非 RH 逼近**；130 轮无伪证明/无公理走私，但 loop 膨胀严重（loop 131 只剩一行组合推论）。
- Claude 核查确认 Sol 三条硬主张：仓库仅 1 commit ✓；Targets.lean 是手填数据账本 ✓（且 `some `foo` 单反引号 Name 字面量不做存在性解析——双反引号才检查）；loop 协议规则可被"自造小目标"游戏化 ✓。
- **v2 协议已发布：`~/Downloads/rh_loop_protocol_v2_20260710.md`，取代 v1 与 repo 内 rh_loop_protocol_20260709.md 的规则部分。核心：暂停 loop 131、双轨道标签（FORMALIZATION/DISCOVERY）、hard_gaps.md 登记表、Targets 三层加固（双反引号+example witness+trusted-primitive audit）、每 loop 一 commit、审计者/实现者分离（5.5 实现、Sol max 每 5 loop 清洁上下文复审、Claude 裁判）。**
- 已执行治理检查点：导出 loop/goal 运行时配置给审计；新增 `research/hard_gap_dag.md`、`research/hard_gaps.md`、`research/loop_classification_20260710.md`；重写 `research/rh_loop_protocol_20260709.md` 的规则部分；新增 `LeanLab/Riemann/TargetChecks.lean` 并接入 build；`T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` 标记为机械 batch item。

## M0 清洁上下文审计（2026-07-10）
- `AUDIT-20260710-M0-01` 已由 Lean 证明 `nymanBeurlingConcreteApprox_unconditional`：unrestricted 谓词允许参数 `1` 和 `-1`，两者的 fractional-part kernel 在一个可数例外集之外相加为常数一，所以该谓词无需 RH 即成立。
- 结果分类为 `BRANCH_FALSIFIED`，不是 RH progress；详细对齐矩阵见 `research/m0_statement_alignment_20260710.md`。
- `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` 已停放为过时目标；不得把 unrestricted 谓词用于 M1 判据。
- `BATCH-20260710-M0-02` 已证明 restricted closure membership 与项目 restricted concrete tolerance 谓词完全等价；同时 Lean 证明被项目删除的 `(1,∞)` 尾部误差恰等于 `(sum c_k * a_k)^2`。
- 原始文献复核发现 Beurling 1955 的单位区间空间要求 `sum c_k * theta_k = 0`，Balazard-Saias 用 modified generators 编码同一条件；项目 restricted 与 positive-natural local 谓词均遗漏了该矩/尾部条件。
- Batch 02 分类为 `DEPENDENCY_GAP_IDENTIFIED`，不是 RH progress。下一 M0 批次应在 positive-natural finite error 中恢复 squared reciprocal moment；不得把当前 unconstrained local predicate 用于 M1。
- `BATCH-20260710-M0-03` 已定义 `baezDuarteSplitFullLineError` 与 `nymanBeurlingBaezDuarteFullLineConcreteApprox`，保留 `(0,1)` target-one error 和 `(1,∞)` target-zero tail；Lean 证明正规形为 local error 加 reciprocal moment 平方。
- Batch 03 分类为 `FORMALIZATION_ONLY`，不是 RH progress。旧 positive-natural local predicate 只是 full-line predicate 的弱后果；M1 只能使用 full-line predicate。下一 M0 缺口是把 split finite-error 形式包装成 whole-space `Lp` closure，并处理 null endpoint 与 coefficient field。
- `BATCH-20260710-M0-04` 已在真实的实 Hilbert 空间 `L²(0,∞)` 中包装 `chi_(0,1]`、positive-natural kernels、span 与 closure，并由 Lean 证明 `baezDuarteTargetL2_mem_closure_iff_fullLineConcreteApprox`。
- Lean 同时证明 whole-space error 等于 Batch 03 的 split error；`(0,1]` 与 `(0,1)` 的端点差已由无原子体积测度下的积分等式关闭。Batch 04 分类仍为 `FORMALIZATION_ONLY`，M1/G1 与 RH 未改变。M0 只剩 bounded coefficient-field/source-convention audit。
- `BATCH-20260710-M0-05` 已核对 Báez-Duarte 原论文，证明项目 reciprocal kernel 与论文 `rho(1/(n*x))` 公式相同，并在复 `L²(0,∞)` 中包装同一 target、kernels、span 与 closure。
- Lean 证明 `baezDuarteComplexTarget_mem_closure_iff_real`，因此对该实目标与实生成元，允许复系数不改变闭包成员关系；又证明复闭包与 full-line concrete predicate 等价。M0 完成审计见 `research/m0_completion_audit_20260710.md`。
- Batch 05 分类为 `HARD_GAP_REDUCED`：固定节点 M0 已关闭。M1/G1、D 与 RH 仍未证明。后续只允许以 `baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure` 为已对齐的 published criterion carrier，开始 Theorem 1.1 的依赖审计与形式化。
- `AUDIT-20260710-M1-01` 已开始固定节点 M1/G2。Lean 新增 `RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re`，把 mathlib RH 精确转换为论文 Balazard-Saias 引理所需的右半平面零点排除条件。
- mathlib 已有 Mellin、`mellin_eq_fourier`、Fourier `L²` Plancherel，以及仅在 `Re(s)>1` 绝对收敛区的 Möbius L-series 逆公式。它没有论文在临界线附近使用的 RH 条件定量 Möbius 部分和估计，也没有匹配基础 Nyman-Beurling 反向判据的半平面 Hardy/inner-outer/Beurling-Lax 框架。
- Audit 01 分类为 `DEPENDENCY_GAP_IDENTIFIED`，不是 RH progress。完整双方向 DAG 见 `research/m1_baez_duarte_dependency_audit_20260710.md`。下一 M1 批次先查外部 Lean 工程是否已有这两类重依赖；若没有，优先内部形式化 kernel Mellin identity 与 weighted-log `L²` isometry，禁止用 `Re(s)>1` 定理冒充 Balazard-Saias 估计。
- `BATCH-20260710-M1-02` 已完成外部 Lean 审计：未发现 NB/BD 判据或临界带 Möbius 定量估计的现成形式化；`PrimeNumberTheoremAnd` 的 Abel 连续化子图可在本项目 mathlib 上编译，但其整仓含无关未完成模块，因此仅快照 13 个经审计的 Apache-2.0 模块。
- Lean 已证明 `hasMellin_fractionalPartKernel_one`：对 `0 < Re(s) < 1`，`rho(1/x)` 的 Mellin 变换收敛且等于 `-zeta(s)/s`；`hasMellin_baezDuarteKernel` 给出每个 `rho(1/(n*x))` 的 `n^(-s)` 缩放。trusted-dependency 输出仅含 `propext`、`Classical.choice`、`Quot.sound`。
- Batch M1-02 分类为 `HARD_GAP_REDUCED`：G2 的 fractional-kernel Mellin block 已关闭；M1/G1 与 RH 尚未证明。下一固定缺口优先为 weighted-log Fourier-Mellin `L2` isometry，随后才可把现成 Plancherel 接到论文的收敛论证；Möbius 定量估计仍是更重的独立边界。
- `BATCH-20260711-M1-03` 已在 `LeanLab/Riemann/FourierMellin.lean` 中证明 weighted-log 变换 `U(f)(u)=exp(-u/2)f(exp(-u))` 是 `L2(0,∞) ≃ₗᵢ[ℂ] L2(ℝ)`；显式逆代表为 `x^(-1/2)g(-log x)`。证明包含 Jacobian、零测集拉回、两侧可积性、`eLpNorm` 恒等式、复线性、等距性与满射，不依赖未检查前提。
- 已定义 `baezDuarteFourierMellinL2` 与 `mellin_criticalLine_eq_fourier`，把该等距同构接到 mathlib Fourier Plancherel，并核对论文频率 `τ` 对应 mathlib 频率 `τ/(2π)`。trusted-dependency 输出仍仅含 `propext`、`Classical.choice`、`Quot.sound`；全构建 8582 jobs 与占位/显式公理扫描通过。
- Batch M1-03 分类为 `HARD_GAP_REDUCED`：G2 的 weighted-log isometry block 已关闭。下一轮不得继续包装局部 Fourier/Mellin 重写；应在固定 DAG 中选择 source-specific convergence 的精确子边界，或先对 Balazard-Saias/RH-to-Lindelöf 定量依赖做来源和 mathlib 可行性审计。
- `BATCH-20260711-M1-04` 已在 `LeanLab/Riemann/BaezDuarteConvergence.lean` 中证明源文幂次 majorant 在 `beta < 1/2` 时属于 `L2(R)`；同时证明临界线 zeta 零点纵坐标集可数且零测，并证明源文 epsilon 依赖 zeta 比值几乎处处趋于一。
- Batch M1-04 分类为 `DEPENDENCY_GAP_IDENTIFIED`，不是完整收敛或 RH 进展。G2 的宽泛 `source-specific convergence` 已拆为：固定 epsilon 链缺 Balazard-Saias + RH-to-Lindelof 定量界；epsilon 趋零链缺 Lemma 2.2 的统一 zeta 比值界/复 Gamma 竖带比值估计；两链均缺 source-specific weighted-to-unweighted tail transfer。
- 源文 TeX 中 Lemma 2.2 的 Gamma 比值显示式分子分母相同，且大端 tail 指数存在 `1+epsilon`/`1+2*epsilon` 歧义；后续不得静默选定版本。详细矩阵见 `research/m1_source_convergence_boundary_20260711.md`。
- `BATCH-20260711-M1-05` 已从 `f_(delta,n)` 定义由 Lean 证明 `x>1` 时尾指数为 `1+delta`，故 `f_(2*epsilon,n)` 的正确指数是 `1+2*epsilon`；论文式 `forx>1` 的 `1+epsilon` 已确认为排版错误。
- Lean 已在真实 `Lp Real 2 (volume.restrict (Ioi 0))` 上证明：若 `w=x^(-epsilon)f` 且 `f=m/x` 于大端，则 `norm(f)^2 <= (1+2*epsilon)*norm(w)^2`；并证明 epsilon 趋零时的收敛转移及 actual natural-kernel finite-sum 实例。
- Batch M1-05 分类为 `HARD_GAP_REDUCED`：G2/F3 已关闭。前向路线只剩 F1（Balazard-Saias + RH-to-Lindelof）与 F2（Lemma 2.2 + 复 Gamma 竖带比值估计）；反向 base criterion 仍开放。
- `BATCH-20260711-M1-06` 已关闭 G2/F2。项目从 `PrimeNumberTheoremAnd` 同一已审计
  Apache-2.0 commit 原样加入 `Gamma/DigammaSeries.lean`，并在
  `LeanLab/Riemann/BaezDuarteZetaRatio.lean` 中用 digamma 对数增长与 Gronwall 证明复 Gamma
  商界；再由 completed-zeta 函数方程、共轭和零分母分支推出 Baez-Duarte Lemma 2.2 的
  zeta 比值界。显式选择 `epsilon0=1/(8*(C+1))` 后，Lean 证明
  `C*epsilon0<1/2`，并给出支配整个 `[0,epsilon0]` 的单一 `MemLp` 函数。
- Batch M1-06 分类为 `HARD_GAP_REDUCED`，不声称证明 Theorem 1.1 或 RH。G2 前向只剩 F1
  （Balazard-Saias Mobius 部分和估计 + RH-to-Lindelof）；反向 base Nyman-Beurling criterion
  及 Hardy-space factorization 仍开放。详细记录见
  `research/m1_zeta_ratio_digamma_20260711.md`。
- `AUDIT-20260711-M1-07` 复核了 F1 的两条已发表证明路线。Baez-Duarte 原证明使用
  RH-to-Lindelof；Burnol `math/0202166` 的替代证明只需 Balazard-Saias 部分和估计与无条件
  临界线凸性界 `|zeta(1/2+it)|=O(|t|^(1/4))`。因此固定 DAG 已删除 F1 中不必要的
  RH-to-Lindelof 依赖。
- M1-07 分类为 `DEPENDENCY_GAP_IDENTIFIED`，没有新 theorem 被关闭。F1 现在精确剩余：
  (a) Balazard-Saias 定理；(b) 任意指数严格小于 `1/2` 的无条件临界线 zeta 凸性界。
  下一优先目标是后者；当前 Apache-2.0 外部模块只有指数一的线性界，另一个无许可证
  工程把真正的 polynomial-boundary Phragmen-Lindelof 步骤留作 `axiom`，均不能直接复用。
  详细记录见 `research/m1_f1_route_audit_20260711.md`。

- `BATCH-20260711-M1-10` 已把 Balazard-Saias 的完整定量陈述编码为显式 `Prop`，并在该
  前提保持显式的情况下闭合 Burnol consumer chain；固定缺口仍是该定理本身。
- `BATCH-20260711-M1-11` 已读取 Titchmarsh 3.12、14.2、14.25，将源证明拆为截断 Perron、
  `1/zeta` 次幂界、矩形移线三块。新增
  `Complex.exists_differentiableOn_eqOn_exp_comp_of_isSimplyConnected`，从 mathlib 的连续
  lift 无占位推出全纯对数分支及导数 `g'/g`；并新增避开极点 `1` 的 zeta 专用实例。
  本轮分类 `DEPENDENCY_GAP_IDENTIFIED`，`hard_gap_delta=0`。下一固定子目标是形式化
  Titchmarsh 14.2 的 Borel-Caratheodory/Hadamard 论证，得到零点自由内域上的 reciprocal-zeta
  次幂界；在此之前不得跳到 Perron 误差平衡，也不得使用 `Re(s)>1` 绝对收敛替代。
- `BATCH-20260711-M1-12` 已关闭上述固定子边。新增
  `LeanLab/Riemann/ReciprocalZetaSubpower.lean`；主定理
  `RiemannHypothesis.exists_reciprocalZeta_subpower_bound` 在 RH 下对任意
  `0 < delta <= 1/2`、`0 < eta` 给出统一常数 `C > 0`，使
  `1/2+delta <= Re(s) <= 1` 上 `norm (riemannZeta s)^(-1) <= C*(1+|Im(s)|)^eta`。
  路线严格使用 Abel 连续化、M1-11 对数分支、Borel-Caratheodory、由 Mathlib 三线定理
  推出的三圆估计、`delta/2` 几何余量、严格次线性 log 增长及低高度留数/紧致性补丁。
  本轮分类 `HARD_GAP_REDUCED`，只移除 reciprocal-zeta 子边；Balazard-Saias、G2、G1、D 与
  RH 均未完成。下一固定子目标是源等价的 truncated Perron 公式及其统一误差，然后才是
  contour balancing。
- `BATCH-20260711-M1-13` 已审计 Titchmarsh Lemma 3.12/14.25(A)，并新增
  `LeanLab/Riemann/TruncatedPerron.lean`。Lean 已核验右半平面矩形 Cauchy-Goursat、两条水平边
  的显式界、远端右竖边消失，以及 `c=2, 0<y<1` 的定量负侧截断 Perron 核界
  `norm_truncatedPerronKernel_two_le_of_lt_one`。预注册的 Mobius 完整公式尚未完成，本轮分类
  `DEPENDENCY_GAP_IDENTIFIED`、`hard_gap_delta=0`。下一唯一优先依赖是补出矩形穿越 `w=0`
  时 `1/w` 的 `2*pi*i` 留数贡献，从而证明 `y>1` 时 `norm(K_T(y)-1)` 的对应界；之后才允许
  做绝对级数与积分交换、在 `n<x` 处分裂并汇总为 `C*(N+1)^2/T`。
- `BATCH-20260711-M1-14` 已关闭固定子边
  `G2/F1/Balazard-Saias/truncated-Perron`。Lean 明确计算矩形边界的 `1/w` 积分为
  `2*pi*i`，用 `dslope` 补成可去奇点整函数，得到 `y>1` 的 `norm(K_T(y)-1)` 界；随后以
  `Re=5/2` 的可求和 majorant 通过 dominated convergence 交换 Mobius L 级数与区间积分，
  并证明半整数 `x=N+1/2` 满足 `1/|log(x/n)|<=3n`。主定理
  `exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le` 给出绝对常数
  `C*(N+1)^2/T`。本轮分类 `HARD_GAP_REDUCED`；只移除 truncated-Perron，下一固定子边是
  Balazard-Saias 的 contour shifting 与 quantitative error balancing。
- `BATCH-20260711-M1-15` 已关闭上述 contour shifting 与 quantitative error balancing 子边。
  新模块 `LeanLab/Riemann/BalazardSaiasContour.lean` 证明解析倒数的半平面全纯性、可去奇点
  后的矩形留数恒等式、左竖边的对数积分界、两条水平边界及三类幂次平衡；主定理给出 RH 下
  `N^(-delta/3)*(1+|Im(s)|)^eta` 的统一估计，并由 compiled Burnol consumer 移除显式 `hBS`
  前提。本轮分类 `HARD_GAP_REDUCED`，RH 专门化 F1 已关闭；一般 alpha 命题、反向 base
  criterion、G1、D 与 RH 仍开放。
- `BATCH-20260711-M1-16` 已关闭 M0 对齐 strong Baez-Duarte carrier 的反向蕴含。Lean 证明
  ζ 零点处有限自然核和的全 Mellin 变换为零，以 Holder 控制 `(0,1)` 局部误差，精确计算
  `m/x` 尾部，并用 completed-zeta 函数方程反射左侧非平凡零点。主定理
  `baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis` 不依赖一般 Nyman-Beurling 或
  Hardy-space 前提。本轮分类 `HARD_GAP_REDUCED`；下一固定边是把 F1/F2/F3 组装成真正的
  `RH -> closure` 前向定理，M1、G1、D 与 RH 仍开放。
- `BATCH-20260711-M1-17` 已关闭 `G2/forward/fixed-epsilon-natural-convergence`。新模块
  `FourierL2Compat.lean` 用 tempered distributions 和 Fourier-Fubini 证明经典 Fourier 与
  Mathlib 抽象 `L2` Fourier 的兼容；`BaezDuarteForward.lean` 把源码有限 Mobius 和包装进
  `L2`，证明有限 Mellin 公式、Burnol 误差差公式和 Cauchy 范数界。主定理
  `RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2` 在 `0<delta<=1/2` 时给出闭包内
  极限。本轮分类 `HARD_GAP_REDUCED`，但不声称完整前向蕴含。下一固定边应是源码无条件
  `delta -> 0` 收敛到 `baezDuarteTargetL2`，完成后才可组装 `RH -> closure` 和 M1 等价。
  实现提交 `2f1503e` 已通过公开 Lean Action CI run `29154261012`，build job
  `86548687415`。

## Arch 审查（2026-07-09，Claude）
- `BATCH-20260711-M1-18` 已关闭 `G2/forward/delta-to-zero-and-assembly`。新模块
  `BaezDuarteForwardLimit.lean` 证明有限带权公式、固定 epsilon 变换收敛、epsilon-to-zero
  支配收敛、对角选择和精确尾部去权。主定理
  `RiemannHypothesis.baezDuarteComplexTargetL2_mem_kernelClosure` 与 M1-16 合成为
  `riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure`。分类为
  `KNOWN_THEOREM_FORMALIZED`，关闭 M1、G1、G2 与 D；它不提供无条件闭包成员，也不证明 RH。
  实现提交 `0c5f39c` 已通过公开 Lean Action CI run `29156608433`，build job
  `86554644071`。

- 结论：**非盲目瞎猜**。定义正确（riemannXi = 真 ξ 的无极点写法；liCoefficientCandidate = 真 Li 系数下标平移 1）；λ₁ 显式值与文献吻合；attempts 有失败/换招记录；`lake build` 独立复验通过。
- 结构性问题：无北极星定理、改写型 loop 稀释、逐个算 λₙ 按构造到不了 RH、数值事实成本极高（Λ₀(1/2)<4 一个数 = 29 loop）。
- **历史改进方案**：`~/Downloads/review_rh_loop_goal_20260709.md` 曾提出 Tier1/Tier2/Tier3 分层、Targets 账本和 blueprint DAG。V4.1 保留预注册、Targets、DAG 与否决路线记录，删除 RH 禁入与数值 loop 配额；现行规则只认 `research/rh_governance_current.md`。
- **已执行的协议更新**：新增 `LeanLab/Riemann/Targets.lean`、`research/rh_loop_protocol_20260709.md`、`research/blueprint.md`，并更新 `research/riemann_hypothesis_scope.md`。目标账本只记录计划目标，不引入未证 Lean 事实；后续 loop 必须消掉目标账本项、填 blueprint 节点、完成有界库存，或记录明确失败路线。

## RH 下一步
- 已完成 Li/Hadamard 库存，结论是局部工具强、全局 product/zero-enumeration/zero-sum bridge 不足，不适合作为立即 Tier 2 路线；下一步优先调查 Nyman-Beurling/Báez-Duarte 路线。
- 已完成 Nyman-Beurling/Báez-Duarte 库存，结论是没有现成 criterion，但基础 API 足够支撑小型 `L2`/measurability proof nodes；下一步关闭 `T2.pivot`，选择 Nyman-Beurling foundation route。
- 已关闭 `T2.pivot`，当前路线是 Nyman-Beurling foundation route；第一个 Lean 节点已完成：`fractionalPartKernel_memLp_two_unitInterval`。下一步做 `T2.nyman.span.scaffold`，定义由 `fractionalPartKernelL2` 生成的实子模并证明 generator membership。
- 已关闭 `T2.nyman.span.scaffold`；当前已有 `nymanBeurlingKernelSpan` 及 generator membership/minimality。下一步做 `T2.nyman.closure.scaffold`，定义该 span 的拓扑闭包并证明 span 包含于闭包。
- 已关闭 `T2.nyman.closure.scaffold`；当前已有 `nymanBeurlingKernelClosure` 及 span-to-closure/generator-to-closure 基础定理。下一步做 `T2.nyman.density.predicate`，只包装 Hilbert-space 密度陈述，不连接 RH。
- 已关闭 `T2.nyman.density.predicate`；当前已有 `nymanBeurlingKernelDense` 及 closure/top、pointwise closure 两个等价形式。下一步做 `T2.nyman.orthogonal.reformulation`，把密度改写为正交补为零。
- 已关闭 `T2.nyman.orthogonal.reformulation`；当前已有 `nymanBeurlingKernelDense_iff_orthogonal_eq_bot`，把密度改写为正交补为零。下一步做 `T2.nyman.orthogonal.pointwise`，把正交补成员条件展开为对所有 packaged kernel 的内积为零。
- 已关闭 `T2.nyman.orthogonal.pointwise`；当前已有 `mem_nymanBeurlingKernelSpan_orthogonal_iff`，把正交补成员条件展开为对所有 packaged kernel 的内积为零。下一步做 `T2.nyman.density.pointwise`，把密度改写为“所有这类正交向量都是零”。
- 已关闭 `T2.nyman.density.pointwise`；当前已有 `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`，把密度改写为“所有这类正交向量都是零”。下一步做 `T2.nyman.inner.integral.inventory`，库存 `Lp` 内积转积分公式，避免继续只做 Hilbert-space 等价改写。
- 已关闭 `T2.nyman.inner.integral.inventory`；当前已有 `inner_fractionalPartKernelL2_eq_integral`，把 `⟪fractionalPartKernelL2 a, f⟫_ℝ` 改写为 `∫ x, fractionalPartKernel a x * f x`。下一步做 `T2.nyman.density.integral`，把密度障碍命题整体换成积分形式。
- 已关闭 `T2.nyman.density.integral`；当前已有 `nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero`，把密度障碍命题整体换成积分形式。下一步做 `T2.nyman.constant.one.l2`，把常数函数 `1` 包装进 `unitIntervalL2`。
- 已关闭 `T2.nyman.constant.one.l2`；当前已有 `unitIntervalOneL2` 及代表函数定理 `unitIntervalOneL2_coeFn`。下一步做 `T2.nyman.density.one.closure`，在条件 `nymanBeurlingKernelDense` 下推出 `unitIntervalOneL2 ∈ nymanBeurlingKernelClosure`。
- 已关闭 `T2.nyman.density.one.closure`；当前已有 `unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense`。下一步做 `T2.nyman.one.closure.epsilon`，把闭包成员关系改写为由 `nymanBeurlingKernelSpan` 中向量进行 epsilon 距离近似的形式。
- 已关闭 `T2.nyman.one.closure.epsilon`；当前已有 `unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt` 以及密度条件下的 epsilon 近似推论。下一步做 `T2.nyman.span.finite.approx`，把抽象 span 近似元展开为有限实线性组合的 packaged fractional-part kernels。
- 已关闭 `T2.nyman.span.finite.approx`；当前已有有限支撑系数和形式的近似定理 `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt`，以及密度条件下的有限组合近似推论。下一步做 `T2.nyman.finite.approx.norm`，把距离形式改写成差的范数形式。
- 已关闭 `T2.nyman.finite.approx.norm`；当前已有 `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt` 和密度条件下的范数近似推论。下一步做 `T2.nyman.finite.approx.integral.inventory`，库存 `L²` 范数平方转积分的 API，再决定是否能证明局部积分桥。
- 已关闭 `T2.nyman.finite.approx.integral.inventory`；当前已有 `unitIntervalL2_norm_sq_eq_integral_mul_self` 和有限组合差的范数平方积分公式。
- 已关闭 `T2.nyman.finite.approx.representatives`；当前已有有限组合代表元桥、常数一减有限组合代表元桥，以及 concrete squared-error 积分公式。
- 已关闭 `T2.nyman.finite.approx.integral.epsilon`；当前已有密度条件下 concrete squared-error 积分小于 `ε ^ 2` 的有限系数存在定理。
- 已关闭 `T2.nyman.finite.approx.integral.tolerance`；当前已有任意正容差版本的 concrete finite-approximation 存在定理。
- 已关闭 `T2.nyman.baez.duarte.natural.concrete.approx.predicate`；当前已有 positive-natural reciprocal approximation predicate，并已证明它推出 `nymanBeurlingRestrictedConcreteApprox`。v2 协议把 `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` 重分类为机械 batch item，不作为下一轮 standalone research loop。
- trivial-zero 基础包装暂时够用；当前 `λ₁` 的标准形是 `λ₀ * (4 - λ₀) - 2 * deriv completedRiemannZeta₀ 0`，Loop 28 已证明 `λ₁` 虚部为零，Loop 29 已把 `λ₁` 正实部目标改写成纯实数不等式，Loop 30-68 已把函数方程转成中心 Taylor 结构，并把中心化零阶值正性目标进一步改写为 completed-zeta 中心值上界 `< 4` 与 Mellin 侧上界 `< 8`；Loop 39-40 证明该 Mellin modified kernel 在 `0 < x` 上实部非负，且 Mellin 实部本身非负；Loop 41 给出了 integrand 在 `(0,1)` 与 `(1,∞)` 的显式比较上界；Loop 42 已把 Mellin 实部积分拆成两段且证明两段非负；Loop 43 在 majorant 可积假设下把点态比较提升为两段积分比较；Loop 44-46 证明大端 majorant 可积并得到无条件右段积分比较；Loop 47-50 证明小端 majorant 可由近零指数衰减函数支配、原小端 majorant 可积，并得到无条件左段积分比较；Loop 51-52 已合并并简化为全局常数倍指数积分上界；Loop 53-54 证明了小端近零模型的全半线 rpow 换元等式和 `(0,1)` 到全半线标准尾积分的粗上界；Loop 55 已精确计算大端简化指数尾积分；Loop 56 已把左端粗上界积分表示为 `Real.Gamma (1/4)` 的缩放；Loop 57 已合并为只含 `Real.Gamma (1/4)`、`π`、`exp (-π)` 的全局上界；Loop 58 已证明 `Real.Gamma (1/4) ≤ 4`；Loop 59 已证明 `(1/π)^(1/4) ≤ 4/5`；Loop 60 已证明 `exp(-π) < 1/20`；Loop 61 已证明 `exp(-π)/π < 1/20`；Loop 62 已证明 `2*(1-exp(-π))⁻¹ < 17/8`；Loop 63 已证明 Loop 57 的显式 Gamma/指数上界 `< 8`；Loop 64 已证明 Mellin 侧实部 `< 8`；Loop 65 已证明 `0 < (riemannXi (1/2)).re`；Loop 66 已证明 `riemannXi (1/2) ∈ slitPlane`；Loop 67 已证明 `log ∘ riemannXi` 在中心点解析；Loop 68 已证明中心点 `log ∘ riemannXi` 的一阶导数为零；Loop 69 已补上 `riemannXi` 与标准 `completedRiemannZeta` 的桥接；Loop 70 已证明 xi 零点到 zeta 零点的安全方向；Loop 71 已证明带 `Gammaℝ s ≠ 0` 条件的反向桥；Loop 72 已证明非平凡 zeta 零点排除 Gamma 因子零点；Loop 73 已证明项目非平凡 zeta 零点推出本地 `riemannXi` 零点；Loop 74 已包装最终桥 `IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬ IsTrivialZeroPoint s` 并关闭 `T1.xi.zero.bridge`；Loop 75 已把 `λ₁` 正性等价压缩为 `(deriv completedRiemannZeta₀ 0).re < ((λ₀.re)*(4-λ₀.re))/2` 并证明右侧乘积项为正；Loop 76 已把该目标转移到 `WeakFEPair.Λ₀ = mellin f_modif` 层；Loop 77 已用 mathlib 的 Mellin 求导定理把目标转成 log-weighted Mellin 积分实部上界；Loop 78 已把该 Mellin 项拆成 `(0,1)` 与 `(1,∞)` 两段实积分；Loop 79 已证明小端贡献非正并把上界问题压到右段积分；Loop 80 已把右段积分条件式比较到 log-weighted 指数尾 majorant；Loop 81 已证明该 majorant 在 `Ioi 1` 上可积；Loop 82 已把 log-weighted Mellin 实部上界压到显式常数 `(2*(1-exp(-π))⁻¹)*(exp(-π)/π)`；Loop 83 已进一步证明该 Mellin 实部 `< 17/160`；Loop 84 已证明 `17/160` 小于 Li 侧阈值并关闭 `0 < (liCoefficientCandidate 1).re`；Loop 85 已写出 Tier 1 scaffold note。下一步进入 Tier 2 路线库存；不要声称 Li 判据或 RH 等价已经形式化。
- Loop 86 已完成 Li/Hadamard 库存并把立即路线转向 Nyman-Beurling/Báez-Duarte；不要声称 Li 判据或 RH 等价已经形式化。
- 谱路线、随机矩阵和数值证据暂存为启发，不作为证明前提。

## 2026-07-17 H6 Polymath 判据 active checkpoint

- 当前 campaign：`LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`，全局 RH Goal 保持
  active；预注册提交 `8f9425edd6257011b4beea644196053d9ca86d73` 已通过公开 CI run
  `29573972608`、job `87864082110`（`2m02s`）。
- 新模块 `LeanLab/Riemann/DeBruijnNewmanPolymathCriterion.lean` 已编译：三块闭区域、任意复单零点
  局部路径、全虚轴严格正性、三个上界删除、紧致最早接触、左右边界排除、移动下边界等式、
  单/重零点分支消费者、严格 canopy 到通用条带，以及 Table 1 精确算术。
- 活动检查点实现提交 `b4c2f5e24ab35514dccf0f6d85ff40ce43e026c3` 已通过公开 Lean Action
  CI run `29576156216`、job `87870943510`（`3m35s`）；公理审计仅含 `propext`、
  `Classical.choice`、`Quot.sound`。证据提交
  `75861af9619985de90c550779e72862cbd20a210` 也已通过 run `29576446783`、job
  `87871869993`（`1m41s`）。
- Loop 5 已编译 negation/conjugation 除子等价、force 四轨道绝对收敛重排、非接触轨道的
  正则化消去与几何非正性，以及接触代表的精确轨道和。force 分支下一门已缩小为：用单零点
  fiber 基数从 `tsum` 同时剥离四个两两不同的接触索引，并证明余项总和非正。实现提交
  `90fdf2b9039da2a9cdb07758b3a24ab335958018` 已通过公开 CI run `29578060529`、job
  `87876981475`（`2m55s`）。
- Loop 6 已闭合简单接触分支：Lean 用单零点 fiber 基数隔离出四个接触除子索引，证明补集
  `tsum` 虚部非正，得到严格力不等式；再用第一象限对称代表、最早接触边界刚性与时空屏障自动
  推出水平逃逸条件。最终定理 `deBruijnNewmanPolymath_firstBadWitness_not_simple`
  不再需要外部 force 前提。精确 TargetChecks 和七项新公理审计通过，仅使用
  `propext`、`Classical.choice`、`Quot.sound`。实现提交
  `cedbd4d92dcdd05d76b868a95d6fcb2479a3db96` 已通过公开 CI run `29580228443`、job
  `87883895459`（`2m33s`）。
- 尚未证明 Polymath Proposition 3.3、三个区域证书、`Lambda<=0.2` 或 RH。当前唯一精确源障碍是
  重零点向后 Hermite 分裂推出 `deBruijnNewmanHasBackwardUpperLinearEscape`。下一轮只攻击这个接口；
  完整循环记录见 `attempts/h6_polymath_zero_free_criterion.md`。
- Loop 7 新增 `DeBruijnNewmanHermiteSplitting.lean`，已由 Lean 证明后向 Hermite 模型
  `P_(n+1)=X*P_n+2*P_n'` 对每个 `n>=2` 都有严格上半平面零点；奇次情形先用 `divX` 移除零根，
  偶次情形由正常数项排除零根。模型定理通过精确 TargetCheck，三项公理审计仅含 `propext`、
  `Classical.choice`、`Quot.sound`。这还不是实际 `H_s` 的分裂定理。下一精确门是：从重复零点抽取
  有限解析阶 `m>=2`，证明 `sqrt(t-s)` 缩放后的紧致一致极限为 `P_m` 的非零倍数，再把模型上半平面
  根转移为实际零点，从而推出 `deBruijnNewmanHasBackwardUpperLinearEscape`。
- Loop 7 实现提交 `7ac27aa86cd176ef6172b79b3b854724b1243f7a` 已通过公开 Lean Action CI
  run `29582740550`、job `87892131096`（`2m05s`）。

## 2026-07-16 R5 对称平移高斯族本地完成

- 当前 campaign：`CAMPAIGN-20260716-R5-WEIL-SYMMETRIC-GAUSSIAN-FAMILY-01`。
- 新模块 `LeanLab/Riemann/WeilSymmetricGaussianFamily.lean` 已无 `sorry` 编译；主定理为
  `symmetricGaussianXi_arithmetic_explicit_formula`。
- 已抽出通用选高矩形极限 `tendsto_selectedXiRightVerticalIntegralFor`；新族的零点绝对可和、
  顶边消失、两条平移素数核、GammaR 可积性、精确双极点留数和 `b=0` 回归均由 Lean 检查。
- 8,671-job 全构建、Targets、TargetChecks、AxiomsAudit、禁用项扫描与 diff 检查通过；传递公理
  仅 `propext`、`Classical.choice`、`Quot.sound`。
- 分类为 `NEW_RELEVANT_LEAN_THEOREM`，只关闭一个两参数 probe-family 子边；Schwartz/Hermite
  稠密性、tempered distribution、Weil positivity 与 RH 均保持开放。本地 gate 之后按顺序执行
  实现提交、公开 CI、证据回填与 closure。
- 实现提交 `5c4ae54c031a6d999111390694ef738a3da57146` 已通过公开 Lean Action CI run
  `29444276732`（build job `87450715956`，`1m50s`）。证据回填提交
  `ed92d851f0eb697f2b2aec0e1260fe0002ea5bcf` 已通过公开 CI run `29444485950`（build job
  `87451417716`，`1m31s`）。campaign 公开闭合为 `NEW_RELEVANT_LEAN_THEOREM`；全局 RH Goal
  继续 active，下一 campaign 前必须重新执行独立路线选择。

## 2026-07-17 H6 heat-Li 时间单调性本地边界

- Campaign `PROOF-ATTEMPT-20260717-H6-HEAT-LI-TIME-MONOTONICITY-01` 的预注册提交
  `645b4570dfe25bd5bcdcda63168d64a34ba90e24` 已通过公开 CI run `29569013156`，job
  `87848139812`。
- 实际 theta 数值反证门在 80/120/180 位、指标 `0..31`、50 个 `[-16,0]` 时间点上未发现负
  导数；240 位扩展到指标 63、500 位时间零扩展到指标 127 也未发现。全部仅为选题证据。
- 新模块 `DeBruijnNewmanHeatLiMonotonicity.lean` 无条件证明了精确归约：若所有指标的
  `atBot` 极限为零且在 `Iic 0` 上单调不减，则时间零全部 Li 系数非负，继而推出 RH。模块
  没有断言这两个未决前提。
- Lean 同时证明函数级热演化
  `(partial_t F)/F=(1/4)*(deriv(logDeriv F)+(logDeriv F)^2)`。生成函数路线停在无符号的跨指标
  卷积；移动零点路线停在随时间变化的 divisor 类型、碰撞兼容全局标号与 differentiated
  `tsum` 控制。两者都需要尚未得到的 theta 专属全指标符号机制。
- 本地分类 `NO_PROGRESS`，`hard_gap_delta=0`，`route_infrastructure_delta=1`。该猜想未证也
  未否证，H6-E/G8 与 RH 继续 open，全局 Goal 继续 active。完整记录见
  `attempts/h6_heat_li_time_monotonicity.md`。新模块、Targets、TargetChecks、公理审计、禁用项
  扫描和 8,700-job 全构建通过；实现提交
  `fc2a32e8316f59370471597df9a8a26c02480bdd` 已通过公开 CI run `29570628316`、job
  `87853282509`（`2m2s`）；证据提交 `f4a26d5a1ee891099003221b766a2f19a39ab07b`
  已通过公开 CI run `29570843171`、job `87853982402`（`1m45s`）。Campaign 以
  `NO_PROGRESS` 公开闭合，全局 RH Goal 返回价值排序后的新路线选择。

## 2026-07-17 H6 通用条带收缩本地完成

- Campaign `CAMPAIGN-20260717-H6-GENERAL-STRIP-CONTRACTION-01` 的预注册提交
  `2685003e8f6617add0701a2b1680328ca8c4943f` 已通过公开 CI run `29571892273`、job
  `87857388857`（`2m2s`），证明源码随后才开始编辑。
- 新模块 `DeBruijnNewmanGeneralStrip.lean` 精确证明：若 `H_t` 的全部复零点满足
  `Im(z)^2<=muSq` 且 `0<=2*delta<=muSq`，则 `H_(t+delta)` 的全部零点满足
  `Im(z)^2<=muSq-2*delta`；特别地，半宽 `y` 的条带在额外 `y^2/2` 热时间后全部变实。
- 证明沿有限垂直平均、任意基准时刻的热逼近、隔离闭球与 Jensen 圆平均推进，不假设
  单零点、有限零点集或 `t>=0`。两个精确 TargetChecks、Target、五个公理审计、禁用项扫描、
  `git diff --check` 和 8,701-job 全构建均通过；审计公理仅为 `propext`、
  `Classical.choice`、`Quot.sound`。
- 本地分类 `KNOWN_THEOREM_FORMALIZED`，`hard_gap_delta=0`，
  `route_infrastructure_delta=1`。这是已知 de Bruijn 源定理的形式化，不证明
  `Lambda<=0.2`、严格改进、H6-E/G8 或 RH。实现提交
  `9ddee42657933ccd94533affa25f83a75392a1ea` 已通过公开 CI run `29572752471`、job
  `87860124993`（`2m11s`）。证据回填提交
  `307b5e29ed65b909e8efffb126787b9176c93453` 已通过公开 CI run `29572973709`、job
  `87860860348`（`2m7s`）。Campaign 公开闭合为 `KNOWN_THEOREM_FORMALIZED`；全局 RH Goal
  保持 active 并返回价值排序后的新路线选择。

## Arch 审计第五轮（2026-07-18，Claude）：V4.1 首周期，无处方
- 65 commits 全验证：判据 3→5（dBN 全零点实 + Connes-Consani/Yoshida 紧算术 Weil）；H6 上半界端点 `deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul` 关闭；Rodgers-Tao 未走私为前提（仅文献引用）✓；四模式全真实运转（含两次自我证伪：positive-cosh Li3、XiKernel PF5）；README/查新/上游队列落地且措辞纪律优秀。
- 完整性：lake build 8703 全过；公理审计 419 条零非标准；零 sorry。
- 唯一 action（用户侧）：mathlib 政策禁止 AI 撰写公共发言——Zulip 帖与 PR 正文须由用户执笔，机器已备好全部材料（README+查新+队列）。

## 2026-07-18 H6 Polymath 判据 Loop 8 checkpoint

- `DeBruijnNewmanHermiteSplitting.lean` 现已编译：重零点有有限解析重数 `m>=2`，并有全局整函数因子
  `H_t(w)=(w-z)^m*g(w)`、`g(z)!=0`。
- Lean 已证明精确高斯后退热流
  `integral H_t(w+r*y) d gaussianReal(0,2)=H_(t-r^2)(w)`；证明使用仅依赖虚部的复余弦条带界、已有
  theta 核主控和 Fubini 的二维绝对可积性。
- 精确缩放表示
  `H_(t-r^2)(z+r*xi)=r^m*integral (xi+y)^m*g(z+r*(xi+y)) d gaussianReal(0,2)`
  已通过 Lean。它还不是重零点逃逸定理。
- 下一精确门：证明高斯矩多项式等于已编译的 backward Hermite `P_m`，再证紧集一致极限与上半平面根转移。
  `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`、Polymath 判据、`Lambda<=0.2` 和 RH 仍开放。
- 本地门已通过：源文件、Targets、精确 TargetChecks、四项新公理审计、禁用项扫描、`git diff --check`
  以及 `lake build` 的 8,703 个作业全部通过；新端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 实现提交 `549b35e736b9a2de02282bd8ac41bf010b858196` 已通过公开 Lean Action CI run
  `29626216475`、build job `88031047702`（`2m15s`）。

## 2026-07-18 H6 Polymath 判据 Loop 9 checkpoint

- `DeBruijnNewmanHermiteSplitting.lean` 现已编译精确矩恒等式：对任意 `n` 与复数 `xi`，
  `integral (xi+y)^n d gaussianReal(0,2) = P_n(xi)`。证明由复 MGF、高阶导数与 Leibniz
  公式给出，不依赖猜测系数。
- Lean 已证明 `H_t` 在固定水平条带上一致有界；重复零点的全局整函数残余因子通过局部
  紧性与远处因子分解继承该界。这排除了“任意整函数增长”造成的支配漏洞。
- 缩放残余积分在每个 `(0,xi)` 联合连续，并逐点收敛到 `P_m(xi)*g(z)`。这是真实热流
  缩放族到有限 Hermite 模型的编译极限，不是数值近似。
- 下一精确门是把该极限升级为严格上半平面模型根邻域上的紧集一致收敛，再完成零点转移并
  推出 `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`。
- 当前仍未证明上述逃逸定理、Polymath 判据、`Lambda<=0.2`、H6-E/G8 或 RH；全局 Goal
  保持 active。
- Loop 9 本地源文件、Targets、精确 TargetChecks、四项公理打印、禁用项扫描、
  `git diff --check` 与 8,703-job 全构建通过；新增端点仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。实现提交
  `5e90f7ee9648a55fd10c2ea244741e2fc3254039` 已通过公开 CI run `29627444553`、build job
  `88034514707`（`2m15s`）。

## 2026-07-18 H6 Polymath 判据 Loop 10 本地闭合

- `tendstoUniformlyOn_deBruijnNewman_gaussian_scaled_factor_integral` 已编译：由零尺度紧纤维
  `{0} x K` 上逐点连续性推出任意紧集 `K` 上的一致收敛。
- Lean 将严格上半平面的 backward Hermite 根隔离在满足 `xi.im > rho.im/2` 的闭圆盘中，
  并通过 Jensen 圆平均最小模论证把模型根转移到每个充分小的非零缩放积分。
- 精确缩放恒等式与 `r=sqrt(t-s)` 给出
  `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`；平方根位移超过任意固定线性速度。
- 简单接触与重复接触两支现已同时矛盾，三个预注册端点
  `deBruijnNewmanH_zero_im_abs_lt_of_polymath_regions`、
  `deBruijnNewmanAllZerosReal_add_half_sq_of_polymath_regions`、
  `deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_row` 均通过 Lean。
- 精确 TargetChecks、Targets、新增公理审计、禁用项扫描、`git diff --check` 与 8,703-job
  全构建已通过；传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`。实现提交
  `8be7521652bc46d5f047c8d80fee7f908c04ec56` 已通过公开 CI run `29628757912`、build job
  `88038314365`（`2m26s`）；证据提交 `3eed3f7f201a9e5cb78fb8aa13b1ef2fa4e56838`
  已通过 run `29628894145`、build job `88038690608`（`2m21s`）。campaign 已公开闭合，
  全局 RH Goal 返回价值排序的下一路线选择。
- 这只形式化了“若三块区域证书成立”的已知 Polymath 判据；三块证书、无条件
  `Lambda<=0.2`、H6-E/G8 与 RH 仍开放。全局 RH Goal 保持 active。

## 2026-07-18 H6 Polymath `(xio)` Loop 7 本地闭合

- `deBruijnNewmanRiemannSiegel_xio` 已对每个非整数复数 `s` 编译，精确结论是
  `(1/8)*riemannXi(s)=R_(0,0)(s)+R_(0,0)^*(1-s)`，没有把 `(xio)` 或等价分解作为前提。
- Lean 从实际 Titchmarsh `Phi(a)` 轮廓推出 `(2.10.2)--(2.10.4)`，完成斜 Mellin/Fubini、
  Gamma--zeta 常数核对与半平面恒等式；再以局部一致对数高斯主控证明原始轮廓对参数解析，
  并在非整数域上用恒等定理延拓。
- 六个精确 TargetChecks、六项公理打印、禁用项扫描、`git diff --check` 与 8,712-job 全构建
  通过；新增端点只依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 分类为 `KNOWN_THEOREM_FORMALIZED`，`hard_gap_delta=1`，
  `route_infrastructure_delta=1`。关闭的是已知来源 `(xio)` 依赖，不是 RH；equation `(39)`、
  有效余项估计、严格有限和证书、有限 RH 计算、紧障碍证书、H6-E/G8 与 RH 仍开放。
- 下一精确门是把公开 `(xio)`、有限 `R_(0,0)` 分解和 `(htz)` 组合成 Polymath equation
  `(39)`；本轮只做闭合、公开 CI 与证据回填，不启动下一轮。
- 实现提交 `4be468094a7295778eb50082459f9927f8d0a484` 已通过公开 Lean Action CI run
  `29648023167`、build job `88089442767`（`2m46s`）。

## 2026-07-18 H6 Polymath equation `(39)` Loop 8 预注册

- 本轮是 `PROOF-ATTEMPT`，固定端点为 paper equation `(39)`：对 `t>0`、`z.re!=0` 和任意
  `N`，把 `H_t(z)` 精确写成两个热演化有限和与两个热演化 `R_(0,N)` 余项。
- 项的定义固定为方差二高斯下的水平位移积分
  `E_t(F)(s)=integral F(s+sqrt(t)*y/2) d gaussianReal(0,2)`；Schwarz reflection、
  `(1+iz)/2`、`(1-iz)/2` 与 `Finset.range N` 索引均不可替换。
- 输入 `(htz)`、`(xio)` 和有限分解已经公开 K0。首个新障碍是分别证明实际
  `r_(0,n)`、`R_(0,N)` 在固定非实水平线上的高斯可积性；随后还要用 `y -> -y` 严格证明
  热演化与 Schwarz reflection 交换。
- arXiv `1904.12438v2` 的 TeX 源 lines 487--524 已核对；成功后下一精确门是
  `(rtn-def)`、`(RTN-def)` 的复高斯移线，而不是直接宣称有效估计。
- 预注册必须先通过公开 CI，之后才允许编辑 Loop 8 证明源码；全局 RH Goal 保持 active。

## 2026-07-18 H6 Polymath equation `(39)` Loop 8 本地闭合

- 预注册提交 `a726d2c84395d0c7795ba176f6a884d759749cbb` 已先通过公开 CI run
  `29648603372`、build job `88090965556`（`1m48s`）。
- 新生产模块 `DeBruijnNewmanPolymathRiemannSiegelHeatExpansion.lean` 已编译固定端点
  `deBruijnNewmanH_riemannSiegel_finite_expansion`：对每个 `t>0`、`z.re!=0` 和自然数 `N`，
  `H_t(z)` 精确等于两个热演化有限和与两个热演化余项，即 Polymath equation `(39)`。
- Lean 分别证明了原始轮廓与 Gamma 前因子的可调水平次高斯界、每个实际 `r_(0,n)` 与
  `R_(0,N)` 的方差二高斯可积性、中心高斯在 `y -> -y` 下的不变性，以及热演化与 Schwarz
  reflection 的严格交换；没有把合并后的可积性或 equation `(39)` 当作前提。
- 六个精确 TargetChecks 与五项选定公理打印通过；选定声明只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。禁用项扫描和 `git diff --check` 为空，完整 `lake build`
  的 8,713 个作业通过。实现提交 `af6c80c42c0abdfb1cf91147e74a8b88263b20ea` 已通过公开
  CI run `29651603027`、build job `88098754302`（`2m41s`）；证据提交
  `7cf65e6d19afb963e9bb910a1a0e763a5f234344` 已通过 run `29651774163`、build job
  `88099210841`（`1m55s`）。Loop 8 已公开检查完成。
- 分类 `KNOWN_THEOREM_FORMALIZED`，`hard_gap_delta=1`，`route_infrastructure_delta=1`。
  下一精确源码门是 `(rtn-def)`、`(RTN-def)` 的复高斯移线；有效估计、数值证书、H6-E/G8
  与 RH 仍开放，全局 RH Goal 保持 active。
- Arch 第六轮要求的 `CONTRIBUTIONS.md`、平语摘要与 `VERIFYING.md` 已登记为下一研究轮开始前
  的治理交付，不在本轮公开证据闭环中插入新的证明攻击。

## 2026-07-19 H6 Polymath `(rtn-def)` / `(RTN-def)` Loop 9 本地闭合

- 新增 `DeBruijnNewmanPolymathRiemannSiegelHeatContourShift.lean`。对任意 `t>0`、复数
  `alpha`/`beta`、自然数 `N` 和正整数 `n`，在两个端点位于同一严格开半平面的源码条件下，
  `deBruijnNewmanRiemannSiegelHeatTerm_contour_shift` 与
  `deBruijnNewmanRiemannSiegelHeatRemainder_contour_shift` 编译出精确 `(rtn-def)` 和
  `(RTN-def)`，包括外因子 `exp(-t*q^2/4)`、积分内线性指数和 `t*q/2` 参数平移。
- 证明链先给出实际 raw contour 的 `1/64` 闭条带一致界、远离实轴整数极点的 Gamma
  `1/128` 界及实际 residue/remainder 的 `3/128` 界，再用 `-29/128` 高斯核界使矩形两条
  竖边趋零。有限 Cauchy 矩形、两条长边的 Bochner 极限、实平移和方差二高斯换元随后给出
  完成平方恒等式；generic 轮廓定理最终分别实例化到实际 `R_(0,N)` 与 `r_(0,n)`。
- 新模块、生产导入、Targets、两项精确 TargetChecks 和两项公理打印均通过；禁用项扫描与
  `git diff --check` 为空，全量 `lake build` 的 8,714 个作业通过。两个最终端点仅依赖
  `propext`、`Classical.choice`、`Quot.sound`。
- 实现提交 `74946858f75e27b306cbf43042df74c447b18740` 已通过公开 Lean Action CI run
  `29654348324`、build job `88105922988`（`2m16s`）。分类为
  `KNOWN_THEOREM_FORMALIZED`，`hard_gap_delta=1`，`route_infrastructure_delta=1`。
- 证据提交 `03ccacba97674a8adabf5e2f5b9b6f810539000e` 已通过公开 CI run
  `29654669529`、build job `88106762342`（`1m35s`）；Loop 9 已公开检查完成。
- 本轮移除了闭条带增长、矩形方向、竖边消失和全线极限这组障碍。下一精确源码门是
  Propositions 6.1 与 6.3 的显式 term/remainder 估计；有效常数、严格有限和证书、有限 RH
  输入、紧 barrier winding、H6-E/G8 与 RH 仍开放，全局 RH Goal 保持 active。

## 2026-07-19 H6 Polymath Proposition 6.1 Loop 10 预注册

- Loop 9 closure 提交 `f51a3563cd2fdc19170385fe099d78e3cb0c5b49` 已通过公开 CI run
  `29654773659`、build job `88107035901`（`1m34s`）。
- 已重新下载并校验 arXiv `1904.12438v2` 源码：archive SHA-256
  `1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863`，`debruijn.tex`
  SHA-256 `560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`。Loop 10 固定
  lines 621--678 的 Proposition 6.1，及其 lines 542--606、608--615 的显式前置估计。
- 精确端点采用 `O_<=` 的 witness 语义：对任意实数 `sigma`、`T>10`、正整数 `n` 和
  `0<t<=1/2`，存在复误差 `e`，其范数不超过源码 `(eps-def)`，并使实际
  `deBruijnNewmanRiemannSiegelHeatTerm t n (sigma+iT)` 等于源码 `M_t b_n^t / n^(...)`
  主项乘以 `1+e`。不能把误差写成未定义的大 O 前提。
- 选择 6.1 而暂缓 6.3：6.1 直接进入 `e_A/e_B`，且复用公开 `(rtn-def)`；6.3 还依赖
  Proposition 6.2 的 Arias de Reyna 系数、可测截断阶数及 `RS_K` 显式余项，当前尚无定义。
- 首个障碍是源码 Lemma 5.1(v) 的 Boyd 型复 Stirling 余项。后续还要证明上半平面
  `log M_0`/`alpha` 导数、`Im alpha_n>=-0.15`、线段 Taylor 余项和最终高斯扰动界。
  完整 Proposition 6.1 编译才算成功；任何 prefix 必须移除一个上述实名依赖并按
  `PARTIAL / BLOCKER_EXPOSED` 记账。全局 RH Goal 保持 active。

## Arch 审计第六轮（2026-07-18，Claude）
- 58 commits 全验证：热流 Li 单调性猜想经 500 位/指标 127 数值攻击存活（首个存活原创猜想，标注纪律满分）；λ₃ 正性纯代数证成；Polymath15 流水线组装中（riemannHypothesisUpTo+Table1 3×10¹² 桥+零点自由区判据+Riemann-Siegel 六文件，正攻 eq(39)）——完成则通向 Λ≤0.22 形式化。build 8712 全过；公理审计 466 条零非标准。
- 🔴 Goal 常设职责违规：贡献自述三件套（`~/Downloads/brief_rh_contributions_selfreport_20260718.md`）连续被研究 campaign 挤掉。下一轮必须先出 CONTRIBUTIONS.md/平语摘要/VERIFYING.md，然后再回研究——热流 Li 猜想现在有数值加固，正是放进自述里请专家过目的最佳时机。

## 2026-07-19 H6 Polymath Proposition 6.1 Loop 10 本地检查点

- 预注册提交 `5a9d4ac09317314feba6e9d6482c2336ec941480` 已先通过公开 CI run
  `29655041718`、build job `88107737514`（`1m40s`），证明源码随后才开始编辑。
- 新模块 `DeBruijnNewmanPolymathRiemannSiegelHeatTermEstimate.lean` 无条件编译了上半平面
  `alpha'` 的 `1/(2*Im(s)-6)` 界、`Im(alpha_n)>=-0.15`、同开半平面条件、全 Taylor 线段界、
  `log M_0` 的精确二阶余项、位移平方界、源码主项恒等式和 Gaussian equation `(ax)`。
- 实际 Riemann--Siegel 前因子已严格分解为 `M_0(s)*exp(error(s))`，比值精确等于
  `Gamma(s/2)/GammaStirlingMain(s/2)`。Lean 已检查从 Boyd
  `norm R_2(z)<=0.0205/norm(z)^2` 到相对误差常数 `0.246`、再到主值对数常数 `0.33` 的全部
  分支与算术步骤。
- 完整 Proposition 6.1 尚未证明。当前唯一首个未决义务是直接证明所需区域上的上述 Boyd
  `R_2` 界；项目现有 Gamma 递推、积分、全纯性、粗条带界和 digamma 级数均未提供该有效常数。
  因而本轮分类为 `PARTIAL / BLOCKER_EXPOSED`，`hard_gap_delta=0`，
  `route_infrastructure_delta=1`，没有把条件性消费者登记成 K0。
- 新模块、生产导入、精确 TargetChecks、十项公理打印、禁用项扫描、`git diff --check` 与
  8,715-job 全构建均通过；选定定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 下一轮将预注册直接攻击 Boyd 有效 Stirling 余项的 `PROOF-ATTEMPT`。Proposition 6.1、6.3、
  Table 1 三块证书、H6-E/G8 与 RH 仍开放，全局 RH Goal 保持 active。
- 实现提交 `814083d6c831c4ed18acaf291ce0d64b6199f1da` 已通过公开 Lean Action CI run
  `29657235672`、build job `88113679693`（`2m4s`）。Loop 10 的无条件 prefix 已公开检查，
  `PARTIAL / BLOCKER_EXPOSED` 分类与 Boyd 障碍不变。

## 2026-07-19 H6 Boyd `R_2` Loop 11 预注册

- Loop 10 证据提交 `d656c643194d0685c085f871b1d3c4a159d2f73e` 已通过公开 CI run
  `29657362457`、build job `88114009920`（`1m30s`），Loop 10 已按
  `PARTIAL / BLOCKER_EXPOSED` 公开闭合。
- Loop 11 直接攻击 Polymath Lemma 5.1(v) 的 Boyd 余项：对
  `abs(Im z)>=1 or Re z>=1`，无条件证明实际项目
  `R_2(z)=Gamma(z)/GammaStirlingMain(z)-1-1/(12*z)` 满足
  `norm R_2(z)<=(41/2000)/norm(z)^2`。
- 必须从 Boyd/Nemes 的显式 resurgence 或积分余项表示出发，完成主值复幂分支对齐、绝对可积、
  右半平面界、含 `norm(1-exp(2*pi*i*z))` 的左半平面界、`Im z>=1` 的分母下界、下半平面共轭
  传输及最终常数比较。假设目标界、等价有效 Stirling 前提、未定常数 big O、替代 Gamma、抽样
  或仅正实轴结论均不算成功。
- 主要来源固定为 Boyd 1994 DOI `10.1098/rspa.1994.0158` 的 `(1.13)`、`(3.1)`、`(3.14)`、
  `(3.15)`，并以 Nemes arXiv `1310.0166` 交叉核对现代余项表示。预注册公开 CI 通过前不得
  编辑 Loop 11 证明源码；H6-Q1 与全局 RH Goal 保持 active。
- 预注册提交 `14bdc45fa1a0e70a26e00e57b4bc8325d73d8ad5` 已通过公开 Lean Action CI run
  `29657566566`、build job `88114535307`（`2m10s`），Loop 11 证明源码攻击现已获准开始。

## 2026-07-19 H6 Boyd `R_2` Loop 11 本地检查点

- Nemes arXiv `1310.0166` 源码已核对，TeX SHA-256 为
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`。源码确认 Boyd 的
  resurgence formula `(15)` 只在右半平面给出，而虚轴附近的统一界需要 Nemes Lemma 2 的
  scaled-Gamma 射线估计和 Phragmen--Lindelof 传播。
- 新增 564 行生产模块 `DeBruijnNewmanPolymathBoydStirlingRemainder.lean`。Lean 从项目实际
  `Complex.Gamma` 与主值 Stirling 主项证明共轭、上半平面主项乘积、Gamma 反射乘积、Nemes
  continuation equation `(28)`，以及纯虚轴精确公式
  `norm(Gamma*(i*y))^2=1/(1-exp(-2*pi*y))`。
- 整条虚轴的 `norm(1/Gamma*(i*y))<=1` 已编译；`1/Gamma*` 在开右半平面的可微性和除原点外
  闭右半平面的连续性也已编译。mathlib 的右半平面 Phragmen--Lindelof 定理已接入，所余接口
  被精确压缩为原点连续、亚二次指数增长和正实轴最终有界。
- 左半平面的镜像反射/Stokes 转移已编译：右侧镜像点的 reciprocal scaled-Gamma 界推出
  `norm(Gamma*(z))<=1/(1-exp(-2*pi*Im(z)))`。同时编译了 `Im(z)>=1` 的 `399/400` 分母下界
  与 Boyd 全局 majorant 严格小于 `41/2000` 的常数证明。
- 完整 `deBruijnNewmanPolymathGammaStirlingR2_norm_le` 尚未证明。本轮本地分类为
  `PARTIAL / BLOCKER_EXPOSED`，`hard_gap_delta=0`，`route_infrastructure_delta=1`。首个剩余
  连接边是把 Boyd/Nemes equation `(15)` 作为项目实际 `R_2` 的绝对可积 resurgence 表示并
  完成轮廓旋转；射线子链还需从 Stieltjes 表示闭合上述三个 Phragmen--Lindelof 接口。
- standalone、TargetChecks、七项新增公理打印、禁用项扫描、`git diff --check` 与 8,716-job
  全构建均通过；选定新定理只依赖 `propext`、`Classical.choice`、`Quot.sound`。实现提交
  `3409b7175eb24f1e0f01377795334a08e5f80384` 已通过公开 Lean Action CI run
  `29659089400`、build job `88118485517`（`2m19s`）。Proposition 6.1、6.3、Table 1 证书、
  H6-E/G8 与 RH 均保持 open，全局 Goal active。

## 2026-07-19 H6 Boyd equation `(15)` Loop 12 预注册

- Loop 11 closure-evidence 提交 `ee6a6fcd1130203ec84ee4450b952277e9290db4` 已通过公开 CI run
  `29659211122`、build job `88118794823`（`1m35s`），Loop 11 公开闭合为
  `PARTIAL / BLOCKER_EXPOSED`。
- Loop 12 直接固定 `N=2` Boyd/Nemes equation `(15)`：在 `Re(z)>0` 上，把项目实际
  `R_2(z)` 证明为两个含 `Gamma*(+/- i*s)` 的 `(0,infinity)` Bochner 积分，并证明两核绝对
  可积。完整预注册为 `research/h6_boyd_r2_loop12_prereg_20260719.md`。
- 新攻角不形式化任意阶 Stirling 系数，而复用 Loop 11 的纯虚轴精确模公式控制核；等式部分
  计划从 Euler Gamma 积分的正实轴轮廓分解出发，再用右半平面全纯性延拓。不得假设 equation
  `(15)`、目标 `R_2` 界或等价有效 Stirling 估计。
- 预注册公开 CI 通过前不编辑 Loop 12 证明源码；H6-Q1 与全局 RH Goal 保持 active。
- 预注册提交 `00be4a5bfa3c614482aa4374a177fa73fa3bd131` 已通过公开 CI run
  `29659498616`、build job `88119559667`（`1m31s`），Loop 12 证明源码攻击现已获准开始。

## 2026-07-19 H6 Boyd equation `(15)` Loop 12 本地检查点

- Loop 12 本地分类为 `PARTIAL / BLOCKER_EXPOSED`。新增 453 行生产模块
  `DeBruijnNewmanPolymathBoydR2Integral.lean`，证明对每个 `Re z>0`，两个实际 `N=2`
  Boyd 核都在 `(0,infinity)` 上 Bochner 可积。
- 编译链包括右半平面分母分离和逆范数界、两条 scaled-Gamma 虚轴射线连续性、精确权重模
  平方、全局 majorant `sqrt(s)*exp(-pi*s)`、负射线共轭、保持源码符号的双积分 RHS，以及
  RHS 在正实轴上到单个积分虚部的化简。
- 实际等式 `GammaStirlingR2(z)=BoydR2Integral(z)` 未证明也未假设。Nemes 以引用 Boyd 的
  方式陈述 equation `(15)`；首个剩余依赖是 mathlib 和项目均缺失的全局鞍点坐标/Cauchy
  resurgence 分解。
- 精确 Targets/TargetChecks 和选定公理打印本地通过；新增选定定理只依赖 `propext`、
  `Classical.choice`、`Quot.sound`，禁用证明项扫描为空，`git diff --check` 与 8,717-job 全构建
  通过。公开实现/证据 CI 数据在闭合更新中补录。
- 下一条选定的源码忠实上游边是：用 `t=x*exp(u)` 从 Euler Gamma 积分推出正实轴上的
  `GammaStar(x)` 精确鞍点积分。H6-Q1、Proposition 6.1/6.3、三个 Table 1 证书、H6-E/G8
  和持续 RH Goal 均保持 active。
- 实现提交 `75d39360af35c3fc65ef357b3e4d1aa498c32602` 已通过公开 Lean Action CI run
  `29660452525`、build job `88122109932`（`2m17s`）。保留的 proper prefix 已公开检查；
  Loop 12 分类仍为 `PARTIAL / BLOCKER_EXPOSED`。

## 2026-07-19 H6 Boyd 鞍点积分 Loop 13 预注册

- Loop 12 closure-evidence 提交 `9e8cafdbf9e853d3c811d83dd5ef8eb66d0def69` 已通过公开 CI
  run `29660573269`、build job `88122426325`（`1m29s`），Loop 12 已公开闭合。
- Loop 13 固定下一条上游边：对每个实数 `x>0`，从 Euler Gamma 积分和正缩放 `y=x*t`
  证明项目实际 `GammaStar(x)` 等于 `sqrt(x/(2*pi))` 乘以 phase
  `t-1-log(t)` 的正半轴鞍点积分，并证明该 integrand 在 `(0,infinity)` 可积。
- API 审计确认 mathlib 已有 `Real.Gamma_eq_integral`、`Complex.Gamma_ofReal` 和
  `integral_comp_mul_left_Ioi`。全实轴 `t=exp(u)` 与 Boyd 全局逆鞍点/Cauchy 分解留给后续
  独立边，避免混入未审计的 improper-limit 交换。
- 完整预注册为 `research/h6_boyd_scaled_gamma_saddle_loop13_prereg_20260719.md`。公开预注册
  CI 通过前不编辑 Loop 13 证明源码；H6-Q1 和持续 RH Goal 保持 active。
- 预注册提交 `b7cbdac1eba3ddfef0e1dbc12004210e9e411643` 已通过公开 CI run
  `29660772447`、build job `88122935390`（`1m56s`），Loop 13 证明源码攻击现已获准开始。

## 2026-07-19 H6 Boyd 鞍点积分 Loop 13 本地成果

- Loop 13 本地闭合为 `KNOWN_THEOREM_FORMALIZED`。新增生产模块
  `DeBruijnNewmanPolymathBoydSaddleIntegral.lean`，对每个实数 `x>0` 证明 phase
  `t-1-log(t)` 的正半轴鞍点 integrand 可积，并证明项目实际 `GammaStar(x)` 精确等于
  `sqrt(x/(2*pi))` 乘以该积分。
- 编译链从 Euler 的实 Gamma 积分出发，核验正缩放后的 real-rpow/指数恒等式、正实轴
  principal-branch Stirling main term和平方根归一化。没有把 Boyd/Nemes equation `(15)`、
  `R2` 界、等价有效 Stirling 估计或未说明渐近式作为前提。
- 精确 Targets、双层 TargetChecks、选定公理打印、禁用项扫描和 8,718-job 全构建通过；
  两个登记 spine 只依赖 `propext`、`Classical.choice`、`Quot.sound`。
  `rh_frontier_delta=0`、`route_infrastructure_delta=1`、`engineering_delta=0`。
- 下一条固定边是对 `x>0` 证明全实轴对数坐标公式
  `GammaStar(x)=sqrt(x/(2*pi))*integral_R exp(-x*(exp(u)-u-1)) du`，随后攻击
  `w^2/2=exp(u)-u-1` 的解析逆鞍点与相邻 `2*pi*i` 鞍点像。
- 本轮从 inherited summary 恢复后已重新读取治理、HANDOFF、Targets/TargetChecks、
  AxiomsAudit、attempts 与预注册。模型为 Codex（GPT-5 family；精确 serving variant、
  reasoning effort 与 serving token budget 未暴露）；V4.1 无数值配额。H6-Q1 与持续 RH
  Goal 保持 active。
- 实现提交 `604199086831750112f5cbf189786860e8137755` 已通过公开 Lean Action CI run
  `29661356249`、build job `88124459774`（`1m56s`）。Loop 13 已公开闭合为
  `KNOWN_THEOREM_FORMALIZED`。

## 2026-07-19 H6 Boyd 对数鞍点积分 Loop 14 预注册

- Loop 13 closure-evidence 提交 `ca039c09d2e241e6ff36900d2285dea90fd598d1` 已通过公开 CI
  run `29661467295`、build job `88124766580`（`1m34s`）。
- Loop 14 固定 `t=exp(u)` 的全局一维 Jacobian 换元：对每个 `x>0` 证明
  `exp(-x*(exp(u)-u-1))` 在全实轴可积，并把项目 `GammaStar(x)` 精确改写成该积分。
- 已审计 mathlib 的 `integrableOn_image_iff_integrableOn_abs_deriv_smul` 与
  `integral_image_eq_integral_abs_deriv_smul`；取 `s=univ`、`f=exp` 可一次处理两个无穷端点。
- 完整预注册为 `research/h6_boyd_log_saddle_loop14_prereg_20260719.md`。公开预注册 CI
  通过前不编辑 Loop 14 证明源码；H6-Q1 和持续 RH Goal 保持 active。

## 2026-07-19 H6 Boyd 对数鞍点积分 Loop 14 本地成果

- 预注册提交 `4d21765574a4e43174a8ace7939ea9d585395d9a` 已通过公开 CI run
  `29661631696`、build job `88125198144`（`1m31s`）。
- Loop 14 本地闭合为 `KNOWN_THEOREM_FORMALIZED`。新增生产模块
  `DeBruijnNewmanPolymathBoydLogSaddleIntegral.lean`，用全局一维 Jacobian 定理证明
  `exp(-x*(exp(u)-u-1))` 对每个 `x>0` 在全实轴可积，并把项目实际 `GammaStar(x)` 精确
  改写成该积分。
- 精确 Targets、双层 TargetChecks、选定公理打印、禁用项扫描与 8,719-job 全构建通过；
  新 spine 只依赖 `propext`、`Classical.choice`、`Quot.sound`。
  `rh_frontier_delta=0`、`route_infrastructure_delta=1`、`engineering_delta=0`。
- 下一条固定边是处理复 phase `exp(u)-u-1` 在原点的二重零：构造局部解析平方根因子
  `q(0)=1` 与坐标 `w(u)=u*q(u)`，证明 `w(u)^2/2=exp(u)-u-1`，再证明原点处规范化
  局部解析逆。Boyd equation `(15)`、有效 `R2`、Table 1 证书、H6-E/G8 与 RH 仍 open。
- Loop 14 未检测到新 compaction。模型为 Codex（GPT-5 family；精确 serving variant、
  reasoning effort 与 serving token budget 未暴露）；V4.1 无数值配额。持续 RH Goal active。
- 实现提交 `7578728f6b16544d983f53d68ea0c10f0beb3d42` 已通过公开 Lean Action CI run
  `29661915485`、build job `88125929156`（`2m3s`）。Loop 14 已公开闭合为
  `KNOWN_THEOREM_FORMALIZED`。

## 2026-07-19 H6 Boyd 规范化局部逆 Loop 15 预注册

- Loop 14 closure-evidence 提交 `9724002c25905b4e03cc3db5ccbc34508c1f4f97` 已通过公开 CI
  run `29662032198`、build job `88126225464`（`1m28s`）。
- Loop 15 固定复解析鞍点坐标：从 `exp(u)-u-1` 的三阶 Taylor 精确余项构造原点取值为
  `1` 的 removable factor，定义 `w(u)=u*sqrt(factor(u))`，证明全局平方恒等式、`w'(0)=1`
  以及原点附近的解析局部逆和双向邻域逆。
- API 审计确认 mathlib 已有 `AnalyticAt.exists_eq_sum_add_pow_mul`、complex sqrt 在 slit
  plane 上的解析性、`AnalyticAt.analyticAt_localInverse` 及 strict-derivative 双向局部逆接口。
- 完整预注册为 `research/h6_boyd_local_saddle_inverse_loop15_prereg_20260719.md`。公开预注册
  CI 通过前不编辑 Loop 15 证明源码；H6-Q1 与持续 RH Goal 保持 active。

## 2026-07-19 H6 Boyd 规范化局部逆 Loop 15 本地闭合

- 预注册提交 `8868906756560d3118e5f1d65cbae72dbca1b98c` 已通过公开 Lean Action CI run
  `29662388346`、build job `88127139991`（`1m57s`），随后才开始编辑证明源码。
- 新增生产模块 `LeanLab/Riemann/DeBruijnNewmanPolymathBoydLocalSaddleInverse.lean`。Lean 从
  三阶解析 Taylor 精确余项证明 piecewise factor 在原点的可去解析性，再组合原点附近的
  principal complex sqrt，构造 `w(u)=u*sqrt(factor(u))`。
- 已编译：`w(u)^2/2=exp(u)-u-1` 对所有复数 `u` 成立，`w(0)=0`、`w'(0)=1`，以及一个
  实际定义的局部逆函数在原点解析，并分别在原点邻域满足 `uOfW(w(u))=u` 和
  `w(uOfW(z))=z`。后两条是邻域结论，不宣称该 total representative 全局单射或全局解析。
- 已接入 `LeanLab.lean`、`Targets.lean`、`TargetChecks.lean` 与 `AxiomsAudit.lean`。生产模块
  无诊断，五项选定公理打印只含 `propext`、`Classical.choice`、`Quot.sound`；三项禁止
  构造扫描与 `git diff --check` 为空；全项目 `lake build` 通过（8,720 jobs）。
- 本轮分类 `KNOWN_THEOREM_FORMALIZED`；`rh_frontier_delta=0`、
  `route_infrastructure_delta=1`、`engineering_delta=0`。全局 branch continuation、全局
  injectivity、相邻 `2*pi*i` saddle images、Boyd equation `(15)`、有效 `R2`、Table 1
  证书、H6-E/G8 与 RH 仍 open。
- 下一精确关口是证明规范化坐标沿两条实 saddle rays 的单调性、逆与换元接口，再定位
  首个复延拓 branch obstruction，之后才处理相邻 saddle images。
- 本轮恢复证明工作时继承过一次 compaction summary；恢复后重新核验了当前源码、预注册、
  frontier 与 mathlib API。模型为 Codex（GPT-5 family；精确 serving variant、reasoning
  effort 和 serving token budget 未暴露）；V4.1 无数值配额。H6-Q1 与持续 RH Goal active。
- 实现提交 `016fc4fd71e6b63c142714058547f8b2501fd3a5` 已通过公开 Lean Action CI run
  `29663109048`、build job `88128987815`（`1m53s`）。
- closure-evidence 提交 `60ff744dc89d39980be8460162f4e9a319e0faca` 已通过公开 Lean Action
  CI run `29663259192`、build job `88129384030`（`2m17s`）。Loop 15 已公开闭合；H6-Q1
  与持续 RH Goal 继续 active。

## 2026-07-19 H6 Boyd 实轴全局鞍点微分同胚 Loop 16 预注册

- 最终 Loop 15 ledger 提交 `7f9ed52ede183cb534731cba0a00fb606347ce7a` 已通过公开 Lean
  Action CI run `29663390826`、build job `88129729923`（`1m46s`）。
- Loop 16 固定完整实轴而非另一个局部引理：证明 Loop 15 principal coordinate 的实限制
  `wR` 导数处处为正、严格递增且两端覆盖无穷，构造 `R ~=o R` 的全局逆，证明逆导数，
  再把 Loop 14 积分精确改写成 `exp(-x*w^2/2)` 乘 Jacobian。
- 同轮定位 Boyd source saddles `2*pi*i*n`：对每个非零整数 `n` 证明坐标在该点解析、
  导数为零且坐标平方为 `-4*pi*i*n`。这只登记首批复分支障碍，不宣称全局复逆或
  resurgence contour。
- 已审计 mathlib 的 derivative positivity、两端极限、`StrictMono.orderIsoOfSurjective`、
  `HasDerivAt.of_local_left_inverse`、monotone Jacobian 与 complex slit-plane 接口。完整
  预注册为 `research/h6_boyd_real_saddle_diffeomorphism_loop16_prereg_20260719.md`。
- 公开预注册 CI 通过前不编辑 Loop 16 Lean 证明源码；H6-Q1 与持续 RH Goal active。

## 2026-07-19 H6 Boyd 实轴全局鞍点微分同胚 Loop 16 本地闭合

- 预注册提交 `e21951ecbbf91bfaa7f654027de4e671a45ab525` 已先通过公开 Lean Action CI run
  `29663980567`、build job `88131219843`（`1m33s`），之后才开始编辑证明源码。
- 新增 614 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydRealSaddleDiffeomorphism.lean`。Lean 证明 Loop 15
  principal coordinate 的实限制与复坐标精确一致，removable factor 处处为正，坐标平方给出
  `exp(u)-u-1`，且导数处处为正、两端分别覆盖正负无穷，因而构成 `R ~=o R`。
- 已构造实际全局实逆，证明其导数是正的 reciprocal；再用一维 monotone Jacobian 证明
  Gaussian-Jacobian integrand 可积、其全实积分等于 Loop 14 phase 积分，并回接项目实际
  `GammaStar(x)`。
- 对每个 `n != 0`，Lean 计算 `2*pi*i*n` 处 normalized factor 为 `i/(pi*n)`，证明它属于
  principal sqrt 的 slit plane，继而证明坐标在该点解析、导数为零，且坐标平方为
  `-4*pi*i*n`。特别地 `n=+/-1` 现在给出首批复临界像的编译器证书。
- 两条 Targets、精确 TargetChecks、16 条选定公理打印、禁用项扫描、`git diff --check`
  与全项目 `lake build`（8,721 jobs）通过；新增 spine 只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 分类 `KNOWN_THEOREM_FORMALIZED`；`rh_frontier_delta=0`、`hard_gap_delta=0`、
  `route_infrastructure_delta=1`、`obstruction_map_delta=1`。全局复逆、inverse-Jacobian 的
  Cauchy 系数表示、相邻鞍点分解、Boyd--Nemes equation `(15)`、有效 `R2`、Table 1
  证书、H6-E/G8 与 RH 仍 open。
- 下一精确关口是以已定位的 `n=+/-1` critical images 控制局部逆 Jacobian 的 Cauchy
  展开半径，并证明它们如何产生两项 adjacent-saddle contributions；不得把 equation
  `(15)` 当作前提。
- 本轮恢复时继承过一次 compaction summary，随后重读治理、frontier、源码、日志与 API。
  模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort 与 serving token
  budget 未暴露）；V4.1 无数值配额。H6-Q1 与持续 RH Goal active。
- 实现提交 `59d58270504f26555d6f8771e8a101bda4a115c5` 已通过公开 Lean Action CI run
  `29664724249`、build job `88133120232`（`2m24s`）。closure-evidence 提交
  `8e75db36287768ae8521dc85fdcf101a6b173ffd` 已通过公开 CI run `29664938202`、build job
  `88133668363`（`1m30s`）。Loop 16 已公开闭合；H6-Q1 与持续 RH Goal 继续 active。

## 2026-07-19 H6 Boyd 相邻鞍点 Cauchy 分支 Loop 17 预注册

- Loop 16 最终台账提交 `6b0c58b7374015971a0078d876b7ed86d4fbf724` 已通过公开 Lean
  Action CI run `29665039991`、build job `88133943251`（`1m51s`）。
- Loop 17 以 `PROOF-ATTEMPT` 直接攻击指定复逆分支：在以原点为中心、半径
  `2*sqrt(pi)` 的开圆盘上构造 Loop 15 局部逆的解析延拓，证明相位恒等式、沿两条临界
  射线落到 `n=+/-1` 相邻鞍点，并在每个较小圆盘上得到逆 Jacobian 的 Cauchy 幂级数。
- 同轮必须证明任何与原点分支一致且落到相邻鞍点的解析逆都不能延拓到更大的中心圆盘。
  若全局分支构造受阻，只允许保留完整的临界像范数、临界点无可微局部左逆、恒等定理相位
  延拓与显式 landing 条件下半径障碍 spine；零散 Taylor 系数不算本轮成果。
- Boyd 原文元数据和 Nemes equation `(15)` 已交叉核验；mathlib 有局部解析逆、恒等定理和
  Cauchy 幂级数，但没有适用于该 phase 的现成 monodromy/Lambert-W 分支。完整预注册为
  `research/h6_boyd_adjacent_saddle_cauchy_loop17_prereg_20260719.md`。
- 本轮继承过 compaction summary，已按治理重读权威文件与当前证明边界。模型为 Codex
  （GPT-5 family；精确 serving variant、reasoning effort 与 serving token budget 未暴露）；
  V4.1 无数值配额。H6-Q1 与持续 RH Goal active。
- 公开预注册 CI 通过前不编辑 Loop 17 Lean 证明源码。

## 2026-07-19 H6 Boyd 相邻鞍点 Cauchy 分支 Loop 17 局部结论

- Loop 17 以 `PARTIAL / OBSTRUCTION_RECORDED` 局部关闭。新增生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentSaddleCauchy.lean`，精确计算所有整数
  鞍点像范数平方 `4*pi*|n|`，证明相邻像范数为 `2*sqrt(pi)`，并分类相位的全部临界点。
- Lean 排除了相位值范数小于 `2*pi` 的所有非零临界点，证明非零鞍点不存在可微局部左逆；
  对任意与 Loop 15 局部逆一致的解析圆盘分支，恒等定理强制
  `phase(U(z))=z^2/2`，其 Jacobian 在每个更小闭圆盘上具有 Cauchy 幂级数。
- 若该分支显式落到 `n=+/-1` 相邻鞍点，则 Lean 证明其中心圆盘半径不超过
  `2*sqrt(pi)`。没有构造实际全圆盘分支，也没有证明两个 radial landing，因此不把条件
  半径定理冒充无条件结论。
- 新障碍 `OBS-H6-BOYD-COVERING-CERTIFICATE-01`：还需证明 Boyd 原点鞍点域上的相位特定
  covering/path lifting，排除目标圆盘上的渐近奇异性，并验证相邻等高线边界及其
  `+/-2*pi*i` landing。Boyd 1995 的 Conditions 2.1 正好把唯一 descent path 与 adjacent
  contour boundary 作为几何输入；Gamma 特例只选 `+/-1` 为相邻鞍点。
- `Targets.lean` 记录一个 proven 条件障碍边和一个 in-progress 实际分支边；精确
  `TargetChecks.lean` 与七条公理打印通过，新 spine 仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。分类为 obstruction + route infrastructure：
  `rh_frontier_delta=0`、`hard_gap_delta=0`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。
- 公开预注册提交 `43ffadd881b96aca92ab3f4684612833f9aa15cc` 已通过 Lean Action CI run
  `29665357300`、build job `88134769245`（`1m57s`）；实现提交
  `159ec6c565a3f69cdd4cce5c60fe78d11bab7038` 已通过 run `29666112428`、build job
  `88136696208`（`2m18s`）。实现前本地全项目构建通过 8,722 jobs。Evidence 提交
  `851c9664d9ed92aada42450cfb9b49dcd79955cf` 随后通过 run `29666217582`、build job
  `88136964270`（`1m30s`）；Loop 17 已公开闭合。
- 本轮经历两次 inherited compaction summary，并在每次恢复后重读治理与权威 frontier。
  模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort 与 serving token
  budget 未暴露）；V4.1 无数值配额。H6-Q1 与持续 RH Goal 保持 active。

## 2026-07-19 H6 Boyd 相邻等高线 Loop 18 预注册

- Loop 17 最终 ledger `c7eece5cb1ffaab970c6a4af0643c3f1f2f234fe` 已通过公开 Lean Action
  CI run `29666322004`、build job `88137224007`（`1m30s`）。
- Loop 18 直接攻击 `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的一维几何层。对每个
  `0<=y<=2*pi`，构造方程 `exp(x)*cos(y)=x+1` 在 `[-2,0]` 内的唯一根 `x(y)`，把
  `x(y)+i*y` 证明为从原点到 `2*pi*i` 的零实相位相邻 contour。
- 固定相位高度 `q(y)=exp(x(y))*sin(y)-y`，目标是证明根连续、内部可微，且
  `q'(y)=(x(y)^2+exp(2*x(y))*sin(y)^2)/x(y)<0`，从而得到 `[0,2*pi]` 到
  `[0,-2*pi]` 的唯一 phase lift 和相邻鞍点 landing；下方 contour 由共轭得到。
- 这与 Loop 17 不同：不再枚举临界点，而是验证 Boyd Conditions 2.1 所需的实际 adjacent
  contour。它仍不宣称二维 covering、无渐近奇异性、全圆盘复逆或 equation `(15)`。
- 完整预注册为 `research/h6_boyd_adjacent_contour_loop18_prereg_20260719.md`。本轮继承
  compaction summary 后已重读所有权威 frontier；模型、reasoning effort 和 serving
  budget 的暴露状态不变，V4.1 无数值配额，持续 RH Goal active。
- 公开预注册 CI 转绿前不编辑 Loop 18 Lean 证明源码。

## 2026-07-19 H6 Boyd 相邻等高线 Loop 18 本地闭合

- 公开预注册提交 `54d120eab46217730506e334e24d27aea25da472` 已通过 Lean Action CI run
  `29666526948`、build job `88137742671`（约 `2m12s`），之后才开始编辑证明源码。
- Loop 18 本地闭合为 `PROVED / KNOWN_THEOREM_FORMALIZED`。新增 673 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentContour.lean`，用
  `h(x)=(x+1)*exp(-x)` 在 `x<=0` 上的 order isomorphism 构造全局连续根，避开两个鞍点
  处退化的端点隐函数论证。
- Lean 已证明 `[-2,0]` 内根的存在唯一性、内部精确导数、上方等高线的精确复相位恒等式、
  相位高度的严格递减与端点、唯一相位提升及其 `2*pi*i` 落点；共轭给出下方提升和
  `-2*pi*i` 落点。
- 精确 Targets、十条 TargetChecks、九条选定公理打印、三类禁用项扫描、
  `git diff --check` 与全项目构建（8,723 jobs）通过；新增 spine 仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的相邻边界和一维 landing 子层已关闭；剩余障碍是
  证明两条边界围成原点二维鞍点域、排除目标圆盘上的渐近奇异性并建立 phase-specific
  covering/path lifting，从而构造 disk-wide analytic inverse。
- 分类为 known theorem formalized + route infrastructure：`rh_frontier_delta=0`、
  `hard_gap_delta=0`、`route_infrastructure_delta=1`、`obstruction_map_delta=1`。Boyd--Nemes
  equation `(15)`、有效 `R2`、Table 1 证书、H6-E/G8 与 RH 均仍 open。
- 本轮集成阶段又继承一次 compaction summary，随后已重新读取治理、HANDOFF、Targets、
  TargetChecks、attempt、hard-gap DAG 与预注册。模型为 Codex（GPT-5 family；精确 serving
  variant、reasoning effort 与 serving token budget 未暴露）；V4.1 无数值配额，持续 RH
  Goal active。
- 实现提交 `3b2e050eaab55c41a2f9dc5fffa88e173b284f89` 已通过公开 Lean Action CI run
  `29667229566`、build job `88139688107`（`2m22s`）。本轮实现 spine 已获独立公开复核；
  closure-evidence 提交 `b2d868b60f4510c00f84578af6c61f31a1034188` 也已通过 run
  `29667324379`、build job `88139957737`（`1m33s`）。Loop 18 已公开闭合；最终 ledger
  提交的 CI 证据由本轮收尾记录。

## 2026-07-19 H6 Boyd 规范化坐标径向提升 Loop 19 预注册

- Loop 18 最终 ledger `144efe9c47a414741a22cda807d10f55480fa68b` 已通过公开 Lean Action
  CI run `29667399367`、build job `88140167965`（`1m31s`）。
- Loop 19 继续攻击 residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01`，但目标从相位等高线
  提升到实际 normalized principal coordinate。对 `0<=t<=2*pi`，要证明上、下 contour
  的坐标像分别是从 `0` 到实际相邻临界像 `A_1`、`A_-1` 的精确径向线段。
- 关键新关口是证明 removable factor 沿两条 contour 位于闭右半平面，从而 principal
  complex sqrt 的组合连续且不能换支；仅有 Loop 18 的 coordinate-square 恒等式不足以确定
  符号。
- 计划用 `IsPreconnected.eq_of_sq_eq` 在每个 `[t,2*pi]` 上从临界像端点反向传播平方根
  符号。完整预注册为 `research/h6_boyd_coordinate_rays_loop19_prereg_20260719.md`。
- 本轮无新 compaction；模型、reasoning effort 与 serving budget 的暴露状态不变，V4.1
  无数值配额，H6-Q1 与持续 RH Goal active。
- 公开预注册 CI 转绿前不编辑 Loop 19 Lean 证明源码。

## 2026-07-19 H6 Boyd 规范化坐标径向提升 Loop 19 本地闭合

- 公开预注册提交 `17000cb4a3a9b1eabada3fd35ea4d744fe5520fb` 已通过 Lean Action CI run
  `29667732245`、build job `88141103415`（`1m35s`），之后才开始编辑证明源码。
- Loop 19 本地闭合为 `PROVED / KNOWN_THEOREM_FORMALIZED`。新增 378 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydCoordinateRays.lean`，从
  `phase(u)=s*i` 推出 `re(factor(u))=4*s*re(u)*im(u)/normSq(u^2)`，并用 Loop 18 的上下
  contour 符号证明 factor 沿两条边界均位于闭右半平面。
- 因此 actual principal coordinate 沿两条闭区间连续。Lean 证明坐标提升与实际
  `n=+/-1` 临界像的径向缩放具有相同平方和相同 `t=2*pi` 端点，再用
  `IsPreconnected.eq_of_sq_eq` 排除整段换号，得到两条精确径向恒等式及
  `norm(W(C_+/- (t)))^2=2*t`。
- 精确 Targets、八条 TargetChecks、八条选定公理打印、三类禁用项扫描、
  `git diff --check` 与全项目构建（8,724 jobs）通过；新增 spine 仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的 normalized-coordinate 边界换支与径向
  lift 子层已关闭。剩余障碍完全是二维的：定义两条边界之间的原点鞍点 component，排除
  open target disk 上的 interior asymptotic escape，并建立 proper covering/path lifting。
- 分类为 known theorem formalized + route infrastructure：`rh_frontier_delta=0`、
  `hard_gap_delta=0`、`route_infrastructure_delta=1`、`obstruction_map_delta=1`。disk-wide
  inverse、Boyd--Nemes equation `(15)`、有效 `R2`、Table 1 证书、H6-E/G8 与 RH 均仍 open。
- 本轮无新 compaction。模型为 Codex（GPT-5 family；精确 serving variant、reasoning
  effort 与 serving token budget 未暴露）；V4.1 无数值配额，持续 RH Goal active。
- 实现提交 `7efc4496c89badf7182f6fc6fe81734bb8782924` 已通过公开 Lean Action CI run
  `29668228884`、build job `88142434731`（`2m22s`）。本轮实现 spine 已获独立公开复核；
  closure-evidence 提交 `54aaea3800d7eb39f49f3eb7c7183969af3f0253` 也已通过 run
  `29668328534`、build job `88142709051`（`1m47s`）。Loop 19 已公开闭合；最终 ledger
  提交的 CI 证据由本轮收尾记录。

## 2026-07-19 H6 Boyd 条带相位 properness Loop 20 本地闭合

- Loop 19 最终 ledger `420a009f0f1350beb0f6dbdc8c9aa38d3c2a71d7` 已通过公开 Lean Action
  CI run `29668411637`、build job `88142934757`（`2m0s`）。Loop 20 预注册提交
  `0aa33d4a8a3cd1a78de7a46faf90e9d4d87d8fa4` 随后通过 run `29668684962`、build job
  `88143662554`（`2m11s`），之后才开始编辑证明源码。
- Loop 20 本地闭合为 `PROVED / HARD_GAP_REDUCED`。新增 247 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydStripProperness.lean`，把
  `phase(u)=exp(u)-u-1` 限制到 `|Im u|<2*pi` 且 `norm(phase(u))<2*pi` 的来源域，并定义
  到半径 `2*pi` 开圆盘的实际 subtype 映射。
- Lean 精确证明两条条带边界上的 phase norm 至少为 `2*pi`；对每个非负闭子水平集给出
  实部上下界并用 Heine--Borel 证明紧致。对目标开圆盘中的任意紧集，Lean 取其范数最大值
  得到严格半径余量，再证明全部条带逆像紧致，最终编译
  `IsProperMap deBruijnNewmanPolymathBoydPhaseOnOriginDomain`。
- 这关闭了 `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的内部渐近逃逸层。剩余障碍不再是
  properness，而是证明来源域为原点连通分支、把 phase 的 proper holomorphic map 次数
  算成二，并将原点二重分歧覆盖提升为 normalized coordinate 的单叶解析逆。
- 精确 Targets、六条 TargetChecks、六条选定公理打印、三类禁用项扫描、
  `git diff --check` 与全项目构建（8,725 jobs）通过；新增 spine 仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 分类为 source-specific hard-gap reduction + route infrastructure：
  `rh_frontier_delta=0`、`hard_gap_delta=1`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。Boyd--Nemes equation `(15)`、有效 `R2`、Table 1 证书、
  H6-E/G8 与 RH 仍 open。
- 本轮从一次 inherited compaction summary 恢复并重读全部权威 frontier；此后无新
  compaction。模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort 与
  serving token budget 未暴露），V4.1 无数值配额，持续 RH Goal active。
- 实现提交 `0ba680319f11c9bcd8647a1c9501002987ea61ec` 已通过公开 Lean Action CI run
  `29669163075`、build job `88144972286`（`2m17s`）。closure-evidence 提交
  `7691e3353161c8f9ead1f726517900adf8ec7018` 也已通过 run `29669268220`、build job
  `88145255930`（`1m47s`）。Loop 20 已公开闭合；最终 ledger CI 由本轮收尾记录。

## 2026-07-19 H6 Boyd 相位来源域连通性 Loop 21 预注册

- Loop 20 最终 ledger `8fae21e1af69095ab2c7fefa3763957e61505365` 已通过公开 Lean
  Action CI run `29669353109`、build job `88145481490`（`1m46s`）。
- Loop 21 固定 residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的来源域连通与满射层：先证明
  `exp(u)-u-1` 在 `|Im u|<2*pi` 内只有零点 `u=0`，再证明 Loop 20 实际 subtype 相位映射
  为开映射。
- 新攻击不是直接猜来源域星形，而是结合 Loop 20 properness 给出的闭映射与 mathlib 的
  open+closed map 连通分支基数定理。目标零点纤维为 singleton 将迫使来源域只有一个连通
  分支；非空 clopen range 随后给出到整个目标开圆盘的满射。
- 本轮不宣称 phase degree two、来源域单连通、normalized coordinate 全局单叶或
  Boyd--Nemes equation `(15)`。完整预注册为
  `research/h6_boyd_phase_domain_connectedness_loop21_prereg_20260719.md`。
- Downloads 中的 `RH_GOVERNANCE_V4_PATCH.zip` 已校验为仓库现有 Sol V4 适配导入的同一
  文件；V4.1 对旧 proof freeze、cooldown、配额和审批闸门的废除继续有效，无冲突待裁决。
- 本轮从 inherited compaction summary 恢复并已重读治理与权威 frontier。模型为 Codex
  （GPT-5 family；精确 serving variant、reasoning effort 与 serving token budget 未暴露）；
  V4.1 无数值配额，H6-Q1 与持续 RH Goal active。
- 公开预注册 CI 转绿前不编辑 Loop 21 Lean 证明源码。

## 2026-07-19 H6 Boyd 相位来源域连通性 Loop 21 本地闭合

- 公开预注册提交 `23e977591546a0962562405515a02979e1881b4e` 已通过 Lean Action CI run
  `29669918676`、build job `88146935055`（`2m1s`），之后才开始编辑证明源码。
- Loop 21 本地闭合为 `PROVED / HARD_GAP_REDUCED`。新增 258 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydPhaseDomainConnectedness.lean`，Lean 证明
  `exp(u)-u-1` 在 `|Im u|<2*pi` 内只有原点零点，并由 complex open mapping theorem 得到
  全局与实际 subtype 相位映射均为开映射。
- Loop 20 properness 给出闭映射；mathlib 的 open+closed map 连通分支基数定理把来源域分支
  数压到零点纤维基数，而该纤维已精确证明为 singleton。因此来源域连通，且相位的非空
  clopen range 必为整个连通目标开圆盘，得到实际满射。
- 精确 Targets、六条 TargetChecks、六条选定公理打印、三类禁用项扫描与全项目构建
  （8,726 jobs）通过；新增 spine 仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- residual `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的 connected-origin-component 与
  phase-surjectivity 层已关闭。剩余关口是证明 proper holomorphic phase map 的 branched
  degree 为二，再将其提升为 normalized coordinate 的 disk-wide 单叶解析逆；不得从原点
  二重零点直接跳到全局 degree two。
- 分类为 source-specific hard-gap reduction + route infrastructure：`rh_frontier_delta=0`、
  `hard_gap_delta=1`、`route_infrastructure_delta=1`、`obstruction_map_delta=1`。
  Boyd--Nemes equation `(15)`、有效 `R2`、Table 1 证书、H6-E/G8 与 RH 均仍 open。
- 本轮从 inherited compaction summary 恢复并重读全部权威 frontier；此后无新 compaction。
  模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort 与 serving token
  budget 未暴露），V4.1 无数值配额，持续 RH Goal active。
- 实现提交 `838e07a2c6d0b2ed10194b3c03170a5a99f375a0` 已通过公开 Lean Action CI run
  `29670331447`、build job `88148019006`（`2m16s`）。closure-evidence 提交
  `1579ae7a1d82726b0975c2742fcb87753e74ef92` 也已通过 run `29670422956`、build job
  `88148267994`（`1m51s`）。Loop 21 已公开闭合；最终 ledger CI 由本轮收尾记录。

## Arch 审计第七轮（2026-07-19，Claude）
- 47 commits 全验证：eq(39) 关闭（H_t 热展开精确分解+反射交换，零前提）；推进 Polymath Prop 6.1；Boyd 最速下降弧线 13 loop（鞍点坐标/Stirling 余项——mathlib 空白区开荒）；三件套按规格完成（24 出处标签+Claim Boundary+反模型章+待查新归约章）。build 8726 全过；公理审计 554 条零非标准。
- 状态：曝光债务清偿完毕，Zulip 发布只等用户。研究侧无处方，Boyd 弧线方向正确（通向 Prop 6.1 有效界→Λ≤0.22）。

## 2026-07-20 H6 Boyd 相位分歧次数二 Loop 22 公开闭合

- Loop 22 以 `PROOF-ATTEMPT` 局部闭合 residual
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01` 的次数计算层。新增 535 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBranchedDegreeTwo.lean`。
- Lean 把解析逆函数定理通过实际 `D -> B` 两个 subtype 封装为局部 open partial
  homeomorphism；Loop 20 properness 使正则纤维紧致，局部同胚使其离散，因而得到实际
  `IsCoveringMapOn Phi ({0}^c)` 与穿孔 subtype covering。
- 对正实相位，Lean 从虚部方程排除全部非实原像。相位 `1` 的完整纤维随后由 Loop 16
  全局实坐标同胚精确识别为 `W_R^-1(-sqrt(2))` 和 `W_R^-1(sqrt(2))` 两个不同点。
- mathlib 的 open-ball homeomorphism 把 `C \ {0}` 的路径连通性搬到穿孔目标圆盘；covering
  monodromy 再把基准纤维双射到任意非零纤维，最终编译所有非零 `z in B` 上
  `Nat.card(Phi^-1({z}))=2`。
- 汇总定理
  `deBruijnNewmanPolymathBoydPhaseOnOriginDomain_branchedDegreeTwoCertificate` 同时记录原点
  二重解析零点、singleton 零纤维、域内唯一临界点与所有正则纤维精确二点。
- 精确 Targets、七条 TargetChecks、六条选定公理打印与三类禁用项扫描通过；新增 spine
  仅依赖 `propext`、`Classical.choice`、`Quot.sound`。本地全项目 build 的 8,727 个任务全部
  通过；公开实现与 closure-evidence CI 也已通过。
- residual 不再是次数或 properness：下一精确关口是把该二重 phase covering 与穿孔平方
  映射 covering 比较，构造与 Loop 15 原点局部分支一致的全局 normalized-coordinate lift，
  跨原点延拓并证明 disk-wide 解析逆；本轮不宣称此 lift 或 Boyd--Nemes equation `(15)`。
- 分类 `PROVED / HARD_GAP_REDUCED`：`rh_frontier_delta=0`、`hard_gap_delta=1`、
  `route_infrastructure_delta=1`、`obstruction_map_delta=1`。H6-Q1、equation `(15)`、有效
  `R2`、Table 1 证书、H6-E/G8 与 RH 仍 open。
- 公开预注册提交 `79ec959` 已先通过 Lean Action CI run `29719851304`、build job
  `88280405198`（`1m44s`），之后才编辑证明源码。本轮从一次 inherited compaction summary
  恢复并重读全部权威 frontier；此后无新 compaction。模型为 Codex（GPT-5 family；精确
  serving variant、reasoning effort 与 serving token budget 未暴露），V4.1 无数值配额，
  持续 RH Goal active。
- 实现提交 `3768a0cc4ac8e3f1138ed9f958fe5c5dbac4b983` 已通过公开 Lean Action CI run
  `29721424614`、build job `88285064009`（`2m0s`）。closure-evidence 提交
  `12fcc3b1aa7437e74083123bfb15ea43fe72bc8e` 也已通过 run `29721623535`、build job
  `88285645538`（`1m49s`）；Loop 22 因而公开闭合。

## 2026-07-20 H6 Boyd 全局归一化坐标 Loop 23 本地闭合

- Loop 23 以 `PROOF-ATTEMPT` 局部闭合
  `OBS-H6-BOYD-COVERING-CERTIFICATE-01`。新增 1,184 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydNormalizedCoordinate.lean`。
- 首先完整编译了 principal square-root 路线的条件式证明链：若 removable factor 在实际
  相位域内处处属于 `Complex.slitPlane`，则 principal coordinate 连续、proper、为 covering，
  并给出全局同胚及解析逆。该 no-cut 前提没有被假设或提升。
- 成功的无条件路线利用更强的域结构：removable factor 在整个凸条带
  `|Im u|<2*pi` 上解析且无零点。Lean 的 simply-connected analytic-log 定理给出解析
  logarithm；其一半的指数再用原点值归一化，得到 `root(0)=1` 且 `root^2=factor` 的全局
  平方根。
- 新坐标满足 `coordinate(u)^2/2=phase(u)`。由 Loop 22 前已编译的相位临界点分类，Lean
  排除坐标导数在实际相位域内为零。解析逆函数局部图加 Loop 20 phase properness 使坐标
  成为 natural coordinate disk 上的 covering。
- 目标圆盘可缩；covering identity lift 给出全局双侧逆，从而得到无条件
  `D ≃ₜ W`。在每个目标点再与解析逆函数定理的局部分支比较，证明环境逆函数在整个
  `W` 内逐点解析。
- Lean 还证明 global square root 与 Loop 15 principal root 在原点邻域同号，因此全局坐标
  与 Loop 15 坐标 germ 相同；利用全局同胚单射性，disk inverse 与 Loop 15 local inverse
  germ 也相同。汇总定理
  `deBruijnNewmanPolymathBoydNormalizedCoordinateGlobalCertificate` 同时暴露平方恒等式、
  双侧逆、disk-wide analytic inverse 与两项 germ 一致性。
- 精确 Targets、八条 TargetChecks、八条选定公理打印、生产源码禁用项扫描、
  `git diff --check` 与全项目构建（8,728 jobs）通过；新增 spine 仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 分类为 `PROVED / HARD_GAP_REDUCED`：`rh_frontier_delta=0`、`hard_gap_delta=1`、
  `route_infrastructure_delta=1`、`obstruction_map_delta=1`。下一精确关口是利用 disk-wide
  analytic inverse 及其导数建立 inverse-Jacobian adjacent-saddle decomposition，再连接
  Boyd--Nemes equation `(15)` 与有效 `R2`；H6-Q1 和 RH 仍 open。
- 公开预注册提交 `02ff528c5ce2a4c63cdd32f8c65238ec795d08d3` 已在证明源码编辑前通过
  Lean Action CI run `29722372082`、build job `88287886054`（`1m32s`）。实现提交
  `ddf586efa892d4406908cce4fd8db591b87dbbe4` 已通过 run `29724881068`、build job
  `88295578003`（`1m57s`）；closure-evidence 提交
  `6ec48e0250b7e9abba3cd63888a9692fbd3dedc1` 也已通过 run `29725055352`、build job
  `88296112617`（`1m28s`）。Loop 23 因而公开闭合。
- 本轮从一次 inherited compaction summary 恢复；此后无新 compaction。模型为 Codex
  （GPT-5 family；精确 serving variant、reasoning effort 与 serving token budget 未暴露），
  V4.1 无数值配额，持续 RH Goal active。

## 2026-07-20 H6 Boyd 相邻落点与逆 Jacobian Loop 24 本地闭合

- Loop 24 以 `PROOF-ATTEMPT` 完成 Loop 17 当时因缺少实际全局分支而留下的完整端点。
  新增 691 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentLandingJacobian.lean`。
- 实际 Loop 23 逆分支在完整坐标圆盘上解析，满足 `phase(U(w))=w^2/2`、
  `G'(U(w))*U'(w)=1`、`(exp(U(w))-1)*U'(w)=w` 与 `U'(0)=1`；其 Jacobian 在每个
  `0<r<2*sqrt(pi)` 的圆盘上具有 Cauchy 幂级数。
- Lean 证明两条 Loop 18 contour 在终点前严格位于来源域。全局坐标与 Loop 19 principal
  坐标平方相同，但未据此猜测符号；Loop 23 原点 germ 一致性给出正参数锚点，随后用
  `IsPreconnected.eq_of_sq_eq` 在无零紧区间上传播，得到上下两条实际径向逆公式。
- 两条径向逆公式与 Loop 18 端点连续性给出实际分支到 `2*pi*i`、`-2*pi*i` 的单侧极限。
  对任意更大中心圆盘解析分支，恒等定理迫使它在首个圆盘内等于实际分支；连续性再强制
  临界像处取鞍点值，与 Loop 17 临界导数障碍矛盾。因此无 landing 假设的最大半径
  `R<=2*sqrt(pi)` 已编译。
- 聚合证书为 `deBruijnNewmanPolymathBoydAdjacentLandingJacobianCertificate`。精确 Target、
  TargetChecks、十八条选定公理打印、禁用项扫描、`git diff --check` 与全项目 8,729-task
  build 通过；新增声明只依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 分类 `PROVED / HARD_GAP_REDUCED`：`rh_frontier_delta=0`、`hard_gap_delta=1`、
  `route_infrastructure_delta=1`、`obstruction_map_delta=0`。下一关是从已编译的 inverse
  Jacobian 与相邻边界奇性推导两项 adjacent-saddle contributions、轮廓旋转和 Boyd--Nemes
  equation `(15)`；不得把 `(15)` 或有效 `R_2` 当作前提。
- 公开预注册提交 `a0443b921a48072d889402737c6d38a468eeab71` 已在源码编辑前通过 Lean
  Action CI run `29725851711`、build job `88298656245`（`1m56s`）。实现提交
  `e8ee2a1997a66289459fa7bb0ee1ac7eec3bcef9` 已通过公开 Lean Action CI run
  `29727609529`、build job `88304224149`（`1m58s`）；closure-evidence 提交
  `fc4b716a537448d0630d939cfec44335f6eaaa58` 也已通过 run `29727795315`、build job
  `88304816776`（`2m6s`）。Loop 24 已公开闭合；最终 ledger CI 由本轮收尾记录。
- 本轮共从两次 inherited compaction summary 恢复。第一次在选题与证明阶段，第二次在本地
  build 和初始日志完成后的集成阶段；两次恢复后均重新读取治理、HANDOFF、Targets、
  TargetChecks、current attempt、hard-gap DAG 与本轮预注册，第二次还复核了 AxiomsAudit，
  然后才进入实现提交。模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort
  与 serving token budget 未暴露），V4.1 无数值配额，H6-Q1 与持续 RH Goal active。

## 2026-07-20 H6 Boyd R2 Jacobian 余项 Loop 25 本地闭合

- Loop 25 以 `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED` 本地闭合；Boyd--Nemes equation `(15)`
  仍为 open，未被假设或宣称证明。
- 新增 1,125 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydR2JacobianRemainder.lean`。Lean 对每个 `x>0`
  证明实际项目 `R2(x)` 等于全实轴 Gaussian 积分中的实际逆 Jacobian 减
  `1-w/3+w^2/12`；三个 Gaussian 矩及积分可积性均精确闭合。
- Lean 从实际方程 `(exp(U)-1)U'=w` 机械推出 `U'(0)=1`、`U''(0)=-1/3`、
  `U'''(0)=1/6`，因此减项系数不是手工选择。
- 两个 Boyd 核被改写为 Stieltjes 核。以 `s^(3/2)*exp(-pi*s)` 为局部统一支配函数，Lean
  证明两个射线积分、完整 Boyd RHS 与实际 `R2` 在 `Re z>0` 复可微；恒等定理随后编译
  equation `(15)` 与一个正实 contour 等式的严格 iff，并进一步化为单个正射线的实标量
  虚部公式。
- 新障碍 `OBS-H6-BOYD-R2-POSITIVE-REAL-CONTOUR-01`：现有复逆仅在首个坐标圆盘解析，真实
  Gaussian 积分却覆盖全实轴；必须构造割平面延拓和两条相邻鞍点 jump，或独立形式化
  source-faithful Binet/Stieltjes 余项公式。mathlib 只有 Euler Gamma 积分，Paris 未证明的
  替代 contour 等价未被采用。
- Targets、九条精确 TargetChecks、八条代表性公理打印、三类禁用项扫描、
  `git diff --check` 与全项目 8,730-task build 均通过；新增代表性定理仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 本轮收到三次 inherited compaction；每次后均重读 canonical governance、HANDOFF、
  Targets/TargetChecks、attempt、DAG 与 Loop25 预注册。模型为 Codex（GPT-5 family；精确
  serving variant、reasoning effort 与 token budget 未暴露）；V4.1 无数值配额，持续 RH
  Goal active。
- 公开预注册提交 `cfc705ad1f4bfedd6973b08226f80b1204791024` 已通过 run
  `29729188057`、job `88309340646`（`2m9s`）。实现提交
  `31b9760e86ddac273caf51f74a34bf8b2a779891` 已通过 run `29733410692`、build job
  `88322989401`（`2m1s`）；closure-evidence 提交
  `69711553db4ce035bf56df2c2b3cbc4fc94b0dee` 也已通过 run `29733618787`、build job
  `88323666807`（`1m55s`）。Loop 25 已公开闭合；最终 ledger CI 由下一轮预注册记录。

## 2026-07-20 H6 Boyd 相邻 Puiseux 跳跃 Loop 26 本地闭合

- Loop 26 本地分类为 `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`。新增 840 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentPuiseuxJump.lean`。
- Lean 在 `+/-2*pi*i` 两个首相邻鞍点构造两张解析 Puiseux sheet，证明共同的精确平移相位
  方程、`eta -> -eta` 换页 involution、两条 phase-Jacobian 链式法则、精确 jump，以及
  `eta*(K^+-K^-) -> 2`。
- Loop 24 的实际上下径向分支经全局坐标生成局部 uniformizer；Lean 证明其趋于零、最终位于
  自然坐标圆盘且非零，并精确识别实际分支为正 sheet，而不是任意选择平方根符号。
- 进一步的 principal slit-plane chart 在 uniformizer 留在首圆盘内时解析并满足
  `h(V)=w^2/2`。但两侧首相邻 chart 在 `w=0` 的 uniformizer norm 都精确等于
  `2*sqrt(pi)`，即现有开圆盘边界；单个 chart 因而不能支撑整条无界 Gaussian contour。
- 新 residual 为 `OBS-H6-BOYD-R2-GLOBAL-CUT-STITCHING-01`：需要相邻/外部逆图拼接、完整割线
  上下边界值与 jump、无界 contour homology 及衰减。Boyd--Nemes equation `(15)`、有效
  `R2`、Table 1、H6-E/G8 与 RH 仍 open，均未被假设。
- 精确 proven Target、八条 TargetChecks、十条选定公理打印、三类禁用项扫描、
  `git diff --check` 与全项目 8,731-job build 通过；选定声明仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 分类增量：`rh_frontier_delta=0`、`hard_gap_delta=1`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。实现提交 `17bae76ae4a4471cc5ca9cc02f59cc6ff39458b1`
  已通过公开 Lean Action run `29737649314`、build job `88336694128`（`2m40s`）；
  closure-evidence 提交 `10be66751465a1c3eebffac127b9242dc71d2ae2` 也已通过 run
  `29737921486`、build job `88337545005`（`2m18s`）。Loop 26 已公开闭合；最终 ledger CI
  由本轮收尾记录。
- 公开预注册提交 `92d945958e1f19ea139227e5226d3aae720e4c7a` 已在源码编辑前通过 run
  `29734964368`、job `88328014471`（`1m52s`）。本轮经历两次 inherited compaction；每次
  恢复后均重读全部权威 frontier。模型为 Codex（GPT-5 family；精确 serving variant、
  reasoning effort 与 token budget 未暴露），V4.1 无数值配额，持续 RH Goal active。

## Arch 审计第八轮（2026-07-19，Claude）
- Loop 21-26 全验证：Puiseux 双叶卡册/换页对合/精确跳跃/全局正规化坐标/R2 Jacobian 归约证成；2√π 卡册边界障碍的发现与登记（OBS-H6-BOYD-R2-GLOBAL-CUT-STITCHING-01）是障碍地图机制的最佳运转样本。build 8731 全过；公理审计 604 条零非标准；零 sorry。研究方向无处方。

## 2026-07-22 H6 Boyd 边界色散 Loop 27 本地闭合

- Loop 27 分类为 `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`。新增 750 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryDispersion.lean`，直接攻击 Boyd--Nemes
  equation `(15)`，但不宣称已经证明该方程。
- Lean 从实际 scaled-Gamma reflection product 证明两条精确虚轴 jump，把 Boyd 的两个
  `exp(-2*pi*s)` 加权 ray 都改写为 `GammaStar(z)-1/GammaStar(-z)`；再按 Nemes 定义精确拆成
  右半平面 `R2(z)` 与左半平面 reflected `inverseR2(-z)`。
- 完整 Boyd `N=2` 积分已精确等于 boundary-jump projection，方向和 `2*pi*i*z` 归一化均由
  Lean 固定。新增通用局部开集矩形 Cauchy 定理，并实例化成左右半平面的有限投影；水平边和
  外竖边全部显式保留。
- canonical rectangle 族把有限投影精确化为 `R2(z)` 减去两个命名 outer-edge residual。
  三项 limit certificate（右 residual 消失、左 residual 消失、内竖边趋于 Boyd jump）一旦成立，
  Lean 即推出 equation `(15)`；该 certificate 本身未证、未假设。
- 新障碍 `OBS-H6-BOYD-R2-BOUNDARY-DISPERSION-LIMITS-01`：需要 complex second-order
  Stirling/closed-half-plane 控制来证明上述三个极限。mathlib 当前没有相应复渐近，项目有效
  `R2` bound 又位于下游条件链，不能在此充当前提。
- 精确 proven Target、八条 TargetChecks、十条选定公理打印、禁用项扫描、`git diff --check`
  与全项目 8,732-job build 通过；选定声明仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 分类增量：`rh_frontier_delta=0`、`hard_gap_delta=1`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。公开预注册提交 `d3d95ed555139112f5826bde32c3bd1a767d499e`
  已在源码编辑前通过 run `29884574692`、job `88812386449`（`1m52s`）；实现提交
  `526f7221dc11f15f8d48a98f02f102a4bce507d2` 已通过 run `29886280505`、build job
  `88817383080`（`2m19s`）。closure-evidence 提交
  `2db6acedf415f0588813f2b8155a3d1d7c1fa2de` 也已通过 run `29886447528`、build job
  `88817871887`（`1m53s`）。Loop 27 已公开闭合；最终 ledger CI 由本轮收尾记录。
- 本轮经历两次 compaction recovery，每次均重读权威 frontier。模型为 Codex（GPT-5 family；
  精确 serving variant、reasoning effort 与 token budget 未暴露），V4.1 无数值配额。局部
  STOP 后按用户安排歇息一轮；H6-Q1 与持续 RH Goal 保持 active。

## 2026-07-22 H6 Boyd 内边界迹 Loop 28 本地闭合

- Loop 28 分类为 `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`，直接攻击 Loop 27 三个极限中的
  inner boundary trace，但未宣称该极限或 Boyd--Nemes equation `(15)` 已证。
- 新增 358 行生产模块 `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryTrace.lean`。Lean
  证明 canonical height 趋于无穷，并利用现有两条 Boyd ray 的可积性证明精确截断趋于完整
  boundary-jump projection。
- Lean 验证左右 offset line 在有限区间可积，并把整个 finite boundary projection 精确写成
  一个 paired vertical-line integral。对每个 `Re z>0` 和非零虚轴坐标，paired integrand
  点态趋于 exact scaled-Gamma reflection-jump kernel。
- 预注册的点态辅助定理漏写了 `Re z>0`；任意 `z` 时 Cauchy 分母可在边界为零。编译版本补上
  此必要假设，而 parent inner-trace target 本来就含该假设，因此主目标没有弱化。
- 聚合证书 `deBruijnNewmanPolymathBoydBoundaryTraceCertificate` 进一步证明：所需 inner trace
  当且仅当单一命名 discrepancy 趋于零。该 discrepancy limit 未证、未假设。
- 新障碍 `OBS-H6-BOYD-R2-BOUNDARY-TRACE-UNIFORM-INTEGRABILITY-01`：需在增长区间上统一控制
  paired offset kernels，同时处理 `w=0` 附近各自 `1/(12*w)` 项的抵消和 `epsilon->0` 时的
  shifted tails。现有虚轴 majorant 不控制偏移值，带增长前提的半平面传播也不能替代。
- 精确 proven Target、六条 TargetChecks、八条选定公理打印、禁用项扫描、`git diff --check`
  与全项目 8,733-job build 通过；选定声明仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 分类增量：`rh_frontier_delta=0`、`hard_gap_delta=1`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。公开预注册提交 `a370945962a2ce4b1e037ae824da24d3edef85bc`
  已在源码编辑前通过 run `29887021780`、job `88819539208`（`2m23s`）；实现提交
  `d7f23c7caa40c14d5f3682722720f863dd3e6438` 已通过 run `29888125681`、build job
  `88822893952`（`2m28s`）。closure-evidence 提交
  `ea2524465f48fa29a1afd73cc2ac4e30b7588de5` 也已通过 run `29888372846`、build job
  `88823638427`（`2m2s`）；Loop 28 已公开闭合，最终 ledger CI 由本轮收尾记录。
- 本轮经历一次 compaction recovery，恢复后重读全部权威 frontier 与完整新源码。模型为
  Codex（GPT-5 family；精确 serving variant、reasoning effort 与 token budget 未暴露），
  V4.1 无数值配额；H6-Q1 与持续 RH Goal 保持 active。

## 2026-07-22 H6 Boyd 边界迹双尺度 Loop 29 本地闭合

- Loop 29 分类为 `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`。新增 884 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryTraceTwoScale.lean`，没有宣称完整 inner
  trace 或 Boyd--Nemes equation `(15)` 已证。
- Lean 在避开原点的每个固定 compact annulus 上证明 paired offset kernel 联合连续，并由
  Heine--Cantor 得到关于 offset 的一致收敛；对应的两个 middle integrals 及 canonical offset
  序列全部趋于零。
- Lean 精确识别 imaginary-axis kernel，把 Loop 28 discrepancy 写成整段 error integral，再
  精确拆成 near、middle、shifted-tail 三项。聚合证书
  `deBruijnNewmanPolymathBoydBoundaryTraceTwoScaleCertificate` 包含最终 iff：完整 discrepancy
  趋零当且仅当 canonical near-plus-tail residual 趋零。
- 继续攻击近零项时，Lean 证明两项显式 `1/(12*w)` 奇性精确抵消成一个
  `epsilon/(6*(w-z)*(q-z))` 有理修正。真正剩余的局部量是 `w*GammaStar(w)` 与
  `w/GammaStar(w)` 的边界估计，而不是未消去的形式极点。
- 原统一可积性障碍被细化为两个 open 子节点：
  `OBS-H6-BOYD-R2-BOUNDARY-TRACE-NEAR-ZERO-SCALED-GAMMA-01` 与
  `OBS-H6-BOYD-R2-BOUNDARY-TRACE-SHIFTED-TAIL-01`。前者需要 shrinking right-half-disk 上的
  统一 scaled-Gamma 边界控制，后者需要 offset 趋零、height 趋无穷时的统一尾界。
- 精确 proven Target、七条 TargetChecks、八条选定公理打印、禁用项扫描、
  `git diff --check` 与全项目 8,734-job build 通过；选定声明仅依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 分类增量：`rh_frontier_delta=0`、`hard_gap_delta=1`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。公开预注册提交
  `436594434b0611d92978a3e7201f8f5f477ecf4c` 已在源码编辑前通过 run `29889067030`、job
  `88825688680`（`1m49s`）；实现提交 `6f34d60701ac696d99b694132d231dc2ab931b62`
  已通过 run `29890689402`、build job `88830378785`（`2m16s`）；closure-evidence 提交
  `ea0c2cec523adbc394af69e3a93674517c765aa4` 已通过 run `29890883349`、build job
  `88830937245`（`2m23s`）。Loop 29 已公开闭合，最终 ledger CI 由本轮收尾记录。
- 本轮经历两次 compaction recovery，每次恢复后均重读治理、HANDOFF、Targets、
  TargetChecks、当前 attempt、DAG、本轮预注册与新源码。模型为 Codex（GPT-5 family；精确
  serving variant、reasoning effort 与 token budget 未暴露），V4.1 无数值配额；H6-Q1 与
  持续 RH Goal 保持 active。

## 2026-07-22 H6 Boyd 边界迹近零消去 Loop 30 本地闭合

- Loop 30 分类为 `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`。新增 613 行生产模块
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryTraceNearZero.lean`；完整 inner trace 与
  Boyd--Nemes equation `(15)` 均未宣称已证。
- Lean 先独立证明复函数 `w*log(w)` 在零点连续，再从 Gamma recurrence 与项目的 principal
  Stirling main term 推出两个全局、含 totalized `w=0` 的精确恒等式：`w*GammaStar(w)` 与
  `1/GammaStar(w)` 都显式含 principal `sqrt(w)` 零因子。因此两者在闭右半平面原点可去。
- 用上述恒等式构造的 pole-free paired kernel 在每个闭右 offset slab 上联合连续；
  Heine--Cantor 随后给出在任意 `[-delta,delta]` 上沿 `nhdsWithin 0 (Ici 0)` 的一致收敛。
  右侧滤子被严格保留，没有跨 principal log/sqrt 的负实轴 branch cut。
- 固定 near residual 与 canonical 正 offset 序列均趋于零。聚合证书
  `deBruijnNewmanPolymathBoydBoundaryTraceNearZeroCertificate` 的最终 iff 把完整 discrepancy
  极限精确归约为 canonical shifted-tail residual 单独趋零。
- `OBS-H6-BOYD-R2-BOUNDARY-TRACE-NEAR-ZERO-SCALED-GAMMA-01` 已闭合；唯一剩余 inner-trace
  子节点是 `OBS-H6-BOYD-R2-BOUNDARY-TRACE-SHIFTED-TAIL-01`。尾部审计确认仅有虚轴精确模长、
  条件式 Phragmen--Lindelof 与假设 `R2` bound 后的推论；仍需非循环的闭半平面二阶复
  Stirling 界，例如在 vanishing-offset lines 上统一 `R2=O((1+y^2)^-1)`。两个 outer-edge
  极限继续独立 open。
- exact proven Target、八条精确 TargetChecks、九条选定公理打印、三类禁用项扫描、
  `git diff --check` 与全项目 8,735-job build 通过；选定声明只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 公开预注册提交 `c56a9cc62744b06b2d82a323b4fc208cb370fe9c` 已在源码编辑前通过 run
  `29891398740`、job `88832391759`（`2m9s`）；实现提交
  `0abfc639e17512316ba2468fbda7f6e84388210e` 已通过公开 run `29892793629`、build job
  `88836454324`（`2m29s`）；closure-evidence 提交
  `f7bea1f2d721e085fd901e5cef7cdd6d5e1b3b78` 也已通过 run `29892965990`、build job
  `88836961122`（`1m39s`）。Loop 30 已公开闭合，最终 ledger CI 由本轮收尾记录。
- 本轮经历一次 compaction recovery，恢复后重读全部权威 frontier 与完整新源码。用户放入
  Downloads 的旧 V4 zip 也已审计：其中 proof freeze/cooldown 条款被后发 V4.1 明确覆盖，
  不会重新应用。模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort 与
  token budget 未暴露），V4.1 无数值配额；H6-Q1 与持续 RH Goal 保持 active。

## Arch 审计第九轮（2026-07-19，Claude）
- Loop 27-30 全验证：面对 2√π 拼接障碍，开辟边界迹第二独立路线（dispersion/trace/two-scale/near-zero 四 loop 闭合），两条解析路线互不假设并进。剩余 inner-trace 子节点=SHIFTED-TAIL（需闭半平面二阶复 Stirling 界）。build 8735 全过；公理审计 639 条零非标准；零 sorry。无处方。

## 2026-07-22 H6 Boyd Stieltjes scaled-Gamma Loop 31 本地闭合

- Loop 31 分类为 `PROVED / KNOWN_THEOREM_FORMALIZED / HARD_GAP_CLOSED`。新增 2,500 行生产
  模块 `LeanLab/Riemann/DeBruijnNewmanPolymathStieltjesScaledGamma.lean`。
- Lean 从有限 unit-block 恒等式、GammaSeq/Bohr--Mollerup 极限与 factorial Stirling 定理重建
  actual project scaled Gamma 的 Stieltjes 表示（Nemes equation `(13)`），没有把 Binet、
  Euler--Maclaurin、复 log-Gamma、`R2` 衰减或 equation `(15)` 当作前提。
- periodic kernel 以均值 `1/12` 中心化后得到
  `|L(z)-1/(12*z)|<=2/|z|^2`；复指数余项进一步给出 direct 和 inverse 两条
  `3/|z|^2` bound。
- indicator dominated convergence 闭合 canonical growing shifted tails；Loop 30/28 的精确
  iff 随即给出 every-cutoff tail、完整 discrepancy 与 inner trace。两个 outer-edge residual
  都有显式 `24*(|z|+n+1)/(n+1)^2` 上界并趋于零。
- `deBruijnNewmanPolymathBoydBoundaryDispersionLimits` 无条件证明三极限 package；
  `deBruijnNewmanPolymathGammaStirlingR2_eq_boyd` 因而证明所有 `Re z>0` 上的 Boyd--Nemes
  equation `(15)`。聚合证书为
  `deBruijnNewmanPolymathStieltjesScaledGammaCertificate`。
- shifted-tail、remaining trace uniform-integrability 与 dispersion-limit 障碍均闭合。全局
  cut-stitching 是已绕过的路线专属问题，不再是 equation `(15)` 的依赖。
- 精确 proven Target、十条 TargetChecks、十一条选定公理打印、禁用项扫描、
  `git diff --check` 与全项目 8,736-job build 通过；选定声明只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- 公开预注册提交 `340e8ebfcf917dd17e03f36a22f2995be62c4058` 已在源码编辑前通过 Lean
  Action run `29893818120`、build job `88839576741`（`1m32s`）。实现提交
  `a0931346a32400e937bbb1333ea355649d8ec101` 已通过公开 run `29916415509`、build job
  `88911217586`（`2m15s`）；closure-evidence 提交
  `785028c7b9efa34c26e9589d3817473f40c18452` 也已通过 run `29916703368`、build job
  `88912167838`（`1m31s`）。Loop 31 已公开闭合，最终 ledger CI 由本轮收尾记录。
- 本轮经历五次 inherited compaction；每次恢复后均重读权威 frontier 与完整当前源码。
  模型为 Codex（GPT-5 family；精确 serving variant、reasoning effort 与 token budget 未
  暴露），V4.1 无数值配额。Loop 31 在公开闭环后局部停止；H6-Q1 下一关是剩余 Table 1
  certificate assembly，H6-E/G8 与持续 RH Goal 保持 active。

## 2026-07-22 Historical Door Survey 路线裁定与预注册

- 用户在 Loop 31 公开闭合后停放 H6/Polymath 数值上界后继，状态为
  `PARKED_BY_USER_DIRECTIVE_20260722`。停放范围包括 effective-`R2`/常数优化与剩余 Table 1
  无条件证书组装；现有 Lean 定理、障碍节点及公开 CI 全部保留。
- 该裁定不把 H6 判为失败，也不关闭 H6-E/G8 的 `Lambda <= 0` 端点。H6-E/G8 与 RH 继续
  open，只是不再作为当前主线。
- 新主线 `LITERATURE-20260722-HISTORICAL-DOOR-SURVEY-01` 是遗漏导向的历史门户普查：逐路
  识别人类最后已证节点、精确缺失对象、历史障碍的现时有效性、可弱化前提、未使用的现代
  工具与跨路线组合，而不是被动汇总文献。
- 用户明确补充：提出、证伪、数值筛查与 Lean 验证精确猜想在任何时候开放。猜想仍走现有
  强度审计与三道闸，不能未经证明成为前提，也不能仅因易做而挤掉普查主线。
- 当前裁定记录为 `research/historical_door_survey_current_20260722.md`，预注册为
  `research/historical_door_survey_prereg_20260722.md`。实质门卡与排序必须等待该预注册提交
  通过公开 CI 后开始。持续 RH Goal active。

## 2026-07-22 Historical Door Survey 本地完成

- 预注册提交 `6aae2d066cddb8978f40b0ec0a8d4a6e7c7bd2ad` 已通过公开 Lean Action run
  `29919775540`、build job `88922071785`（`1m58s`），因此实质普查按门禁合法开始。
- 新增 `research/door_atlas_ranked_20260722.md`，在统一框架下完成 H0-H14、认证计算与
  countermodel 共十三张门卡。每张卡都记录最后已证节点、精确缺失对象、障碍是否仍有效、
  未使用工具、遗漏证据、形式化/机器适配度与至多三个判别探针。
- 普查纠正旧 coverage：H6 应为 `DEEP_FORMALIZATION`；H7/H8/H9/H11/H12/H13/H14 现已在
  本轮 atlas 的边界内达到 `SOURCE_ALIGNED`。这不是声称文献在形而上意义上已穷尽。
- 排名第一是 H5/H7 的 2025-2026 finite-prime Weil ground-state 路线。Connes--van
  Suijlekom 已证明 simple isolated even ground state 的 Fourier transform 全实零点；Connes
  随后明确提出有限素数 Weil 极小向量逼近 Riemann 核。仍缺三关：项目定义对齐、随
  Galerkin/素数 cutoff 一致的 simple-even 谱隙、到 Riemann xi transform 的 compact-uniform
  convergence。高精度数值吻合未被当作证明。
- runner-up 是 2025 short-mollifier derivative-combination optimization。它提供成熟路线中
  曾被低估自由度的直接证据，但没有给出 zeta 的 proportion one；即便比例一成立，稀疏或
  有限个 off-line zeros 仍是独立硬障碍。
- 下一 campaign 建议先做 `H7-WEIL-GROUNDSTATE-ALIGN-01` 的 M0 source alignment，再决定
  对 uniform spectral gap 进入 `PROOF-ATTEMPT` 还是 `FALSIFICATION`。若定义不一致则记录
  mismatch 并转 runner-up，不做非正式修补。
- 本轮分类 `ROUTE_ATLAS_COMPLETED / NEW_OPEN_EDGE_IDENTIFIED`；
  `rh_frontier_delta=0`、`hard_gap_delta=0`、`route_map_delta=1`。没有新增 Lean 数学声明，
  implementation public CI、evidence backfill 与 final ledger CI 尚待完成。一次 inherited
  compaction 已按治理完成全量恢复读取；模型为 Codex GPT-5 family，精确 serving variant、
  reasoning effort 与 token budget 未暴露，V4.1 无数值配额。持续 RH Goal active。

## 2026-07-22 Historical Door Survey implementation CI 通过

- implementation commit `62c813f51020b2c012a4770c204ea97b3893d87e` 已通过公开 Lean
  Action run `29921175166`、build job `88926780992`（`1m49s`）。
- atlas、十三张门卡、source registry、census、DAG、portfolio 与 attempt log 已在公开
  `main` 通过完整构建。分类仍为 `ROUTE_ATLAS_COMPLETED / NEW_OPEN_EDGE_IDENTIFIED`，
  `rh_frontier_delta=0`；下一步是 evidence backfill 及其独立 CI，不提前开始 H7 M0 campaign。

## 2026-07-22 Historical Door Survey 公开闭合

- evidence commit `f8cce8ae32f716cc34087cee5319b23656c8733a` 已通过公开 Lean Action run
  `29921582753`、build job `88928153258`（`1m48s`）。预注册、实现与 closure evidence 三层
  公开证据现均为绿色。
- 本轮保持 `ROUTE_ATLAS_COMPLETED / NEW_OPEN_EDGE_IDENTIFIED`，没有 RH 进展宣称，也没有
  新增 Lean 数学声明。下一步仅提交 final ledger 并等待其 CI；随后本地 survey 停止于成功，
  持续 RH Goal 保持 active，H7 M0 作为独立后继 campaign 再行预注册。
- 本轮共经历两次 inherited compaction；每次恢复均重读治理、HANDOFF、Targets、
  TargetChecks、attempt、DAG、preregistration、外部 ACTIVE 与 git 状态。六份受保护用户/曝光
  文件始终未被本轮修改或暂存。

## 2026-07-22 Historical Door Survey final ledger CI 与 H7 后继启动

- survey final-ledger commit `051ace38c80aebcde083432297c9fa01e02539e4` 已通过公开 Lean
  Action run `29921844064`、build job `88929023824`（`2m1s`）；上一 campaign 完整公开闭合。
- 后继 campaign 为 `LITERATURE-20260722-H7-WEIL-GROUNDSTATE-ALIGN-01`，节点
  `H7-WEIL-GROUNDSTATE-ALIGN-01`。它先逐项对齐来源 `L^2` Weil form、有限 Fourier 矩阵、
  三个 explicit-formula block 与项目的 weighted compact-Laplace autocorrelation，不以同名
  代替定义相等。
- primary-source 重读修正旧 atlas 的粗略表述：Connes 2026 Fact 6.4 已证明显式近似
  `k_lambda` 的 Fourier transform 在闭子条带上一致趋于 Riemann `Xi`；真正未证的是实际最低
  特征向量 `xi_lambda` 对 `k_lambda` 的逼近，以及 simple-even ground-state 条件。
- 2026 年 7 月的 arXiv:2607.02828 声称给出精确、单向的 finite Guinand--Weil dictionary，
  可能闭合 M0 的有限层部分，但不证明逆映射、连续谱性质或 ground-state 极限。该结论先审计，
  不作为前提。
- 候选精确坐标桥是 `g(x)=exp(-x/2)*f(x+L/2)`；它必须由 Lean 验证。来源 pole block 与项目
  `compactWeilArithmeticQuadratic` 的端点矩消去必须分开记录。预注册公开 CI 通过前不编辑
  Lean 证明源码；持续 RH Goal active。

## 2026-07-22 H7 finite-prime Weil M0 本地完成

- 十四项对齐表已写入 `research/h7_weil_groundstate_alignment_20260722.md`；分类为
  `MEANINGFUL_PARTIAL / WEIGHTED_COORDINATE_ALIGNMENT_COMPILED /
  SOURCE_PROJECT_DOMAIN_GAP_EXPOSED`，没有 RH 前沿推进宣称。
- 新模块 `LeanLab/Riemann/WeilGroundStateAlignment.lean` 证明加权中心化根精确共轭来源 star、
  autocorrelation 与项目 compact-Laplace API，并核对临界线与两个 pole moments。
- M0 发现并修正 Fourier 符号：来源采用 `u^(-i*z)`，故来源 `z` 对应项目
  `s=1/2-i*z`；项目 `s=1/2+i*z` 对应来源 `-z`。该关系已由 Lean 编译。
- 精确 project gap 为 `OBS-H7-WEIL-ALIGN-REGULARITY-01`：普通有限 Fourier 向量零延拓后
  通常不在全局 `C infinity` 紧支撑类，不能直接实例化项目 compact criterion；平滑化会改变
  form，不能冒充相等。来源 full form 的 pole block 也不能与项目受约束的 pole-free quadratic
  混同。
- Connes 2026 已证 `k_lambda` transform 趋于 `Xi`；仍未证的是实际最低特征向量
  `xi_lambda` 对 `k_lambda` 的逼近以及 simple-even ground-state 条件。July 2026 finite
  dictionary 是精确但单向的，不给 inverse/density。
- 八条 exact TargetChecks、八项 selected axiom prints 与全项目 `8,737`-job build 本地通过；
  公理仅为 `propext`、`Classical.choice`、`Quot.sound`。实现提交与公开 CI 尚待完成。
- 对齐闭环后建议独立启动 finite matrix/parity formalization，再做 theorem-producing
  `FALSIFICATION` 检查 simple/even uniformity；持续 RH Goal active。
- 实现提交 `0ed05ba49605c7de621f16193ff73dd63a7bbabb` 已通过公开 Lean Action run
  `29924570570`、build job `88938283725`（`1m56s`）。当前只待 evidence backfill 及其独立
  公开 CI；Lean 源码不再改动。
- evidence 提交 `b2c752d730a48d76fadfc5ff1165f3e1240feed6` 已通过公开 run
  `29924847974`、build job `88939252739`（`1m39s`）。本 campaign 已达到注册的
  meaningful-partial 局部停止点；只提交 final ledger 并等待其 CI，持续 RH Goal 不停止。

## 2026-07-22 H7 finite matrix/parity 后继预注册

- alignment final-ledger commit `9ab3bf45101226f731b371a11ec06b149fa11a9a` 已通过公开 Lean
  Action run `29925232284`、build job `88940549581`（`1m55s`）；上一 H7 campaign 已完整闭合。
- 新 campaign 为 `LITERATURE-20260722-H7-WEIL-FINITE-MATRIX-PARITY-01`，节点
  `H7-WEIL-GROUNDSTATE-FINITE-MATRIX-01`。它形式化来源 divided-difference matrix、反射
  奇偶分块，以及严格两块 Rayleigh 条件推出 unique even ground state 的可检查证书。
- 来源 Arb 证书只证明 `c=100,N=200` 整块正定惯性，不证明最低特征值单重或属于 even
  sector；早期负特征值已被来源 ERRATA 判定为有限 archimedean cutoff 伪影。因此目前既不能
  宣称 simple-even 已证，也不能启动证伪结论。
- bounded 数值扫描只作导航。若发现 odd minimum、最低值简并或 parity crossing，必须先转成
  kernel-checked witness，再作为独立 `FALSIFICATION` campaign。有限成功不推出对两个 cutoff
  一致的谱隙。
- 预注册与同步台账先单独提交并通过公开 CI；在此之前不编辑 Lean proof source。历史遗漏
  审计仍为主线，精确猜想提出、筛查和 Lean 验证始终开放；持续 RH Goal active。

## 2026-07-22 H7 finite matrix/parity 本地完成

- campaign `LITERATURE-20260722-H7-WEIL-FINITE-MATRIX-PARITY-01` 达到固定本地端点，分类为
  `KNOWN_SOURCE_STRUCTURE_FORMALIZED / FINITE_CERTIFICATE_INTERFACE`。
- `WeilGroundStateFiniteMatrix.lean` 编译来源有限矩阵、反射/奇偶结构、rank-two commutator、
  二次型分裂，以及严格两块 Rayleigh 条件推出 unique even ground state 的证书。
- arithmetic matrix 的两条严格条件均未证明；`c=100,N=200` Arb 结果仍只给正定惯性。
- 新审计的四份 2026 年 6 月 S3 Zenodo 预印本已经研究 Perron/Loewner 机制，并把完整
  even-simplicity 归约为 pole-localization 与标量条件
  `<S,(B_odd-lambda_even)^(-1)S><1/2`。它们仅登记为来源目标，不作为前提。
- 高精度导航在 `(c,N)=(2,8),(3,8),(5,8),(7,6)` 否定了 universal checkerboard inverse
  positivity；这只淘汰一个朴素猜想，不是 simple-even 的 Lean 反例。
- 556 行生产模块、九条 exact TargetChecks、九项 selected standard-only axiom prints、禁用项
  扫描、`git diff --check` 与全项目 `8,738`-job build 均通过。
- deltas 为 `rh_frontier_delta=0`、`hard_gap_delta=0`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`。公开实现 CI 之后，下一 H7 候选是
  `H7-WEIL-GROUNDSTATE-HERGLOTZ-01`；持续 RH Goal active。
- implementation commit `77ab09b17d371787a8a2d043fd866056de061003` 已通过公开 Lean
  Action run `29930107842`、build job `88957270851`（`2m26s`）。Lean 源码冻结；只待
  immutable evidence backfill、其公开 CI 与 final ledger 闭环。
- evidence commit `27582dbf6f8c28eae870ed57fea07409f1b3a2d2` 已通过公开 Lean Action
  run `29930544524`、build job `88958796486`（`1m54s`）。本 campaign 在注册的 finite
  checker 成功端点停止；只待 final-ledger commit 及其 CI。arithmetic Herglotz inequality、
  uniform simple-even、真实 ground-state 极限与 RH 继续 open。

## 2026-07-22 H7 finite Herglotz criterion 后继预注册

- finite-matrix final-ledger commit `c5ba3ab66e9a61446da7ad43d3a1d3786efd220d` 已通过公开 Lean
  Action run `29930876406`、build job `88959943824`（`1m45s`）；父 campaign 完整闭合。
- 新 campaign 为 `LITERATURE-20260722-H7-WEIL-HERGLOTZ-CRITERION-01`，节点
  `H7-WEIL-GROUNDSTATE-HERGLOTZ-01`。它形式化 odd sector 的 exact rank-one criterion：
  在 `P*u=S` 与 pole-free odd positivity 下，`P-2*S*S^T` 严格正定 iff
  `2*(S dot u)<1`。
- 该 iff 将上一 campaign 的全 odd-vector 条件压缩为一个 source-aligned scalar bound，并
  接回现有 parity Rayleigh certificate。实际 arithmetic scalar inequality 不被假设或宣称。
- 四份直接 Zenodo 来源均为 S3；continuum Perron、Herglotz monotonicity 与数值表不作为
  Lean 前提。有限 completion-of-square identity 与 iff 必须由 kernel 独立证明。
- 只提交 preregistration 与同步台账；公开 CI 通过前不编辑 Lean proof source。历史遗漏审计
  仍为主线，持续 RH Goal active。

## 2026-07-22 H7 finite Herglotz criterion 本地完成

- campaign `LITERATURE-20260722-H7-WEIL-HERGLOTZ-CRITERION-01` 达到固定本地端点，分类为
  `PROVED / KNOWN_FINITE_LINEAR_ALGEBRA_FORMALIZED / SOURCE_ASSUMPTION_WEAKENED /
  FINITE_CERTIFICATE_CONSUMER`。
- `WeilGroundStateHerglotz.lean` 由 completion of squares 独立证明 source sign
  `P-2*S*S^T` 的严格 odd-sector 正性 iff `2*(S dot u)<1`，并接回上一 campaign 的 parity
  Rayleigh 与 simple-even endpoint。
- Lean 暴露一个精确假设弱化：generic iff 不需要 `S` odd，只需 `u` odd 以保证
  `y-2*(S dot y)*u` 仍在 odd sector。source-aligned certificate 仍保留 `odd_S`；这不证明实际
  arithmetic scalar inequality。
- 171 行生产模块、六条 exact TargetChecks、六项 selected axiom prints、禁用项扫描、
  `git diff --check` 与全项目 8,739-job build 均通过；选定声明只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- deltas 为 `rh_frontier_delta=0`、`hard_gap_delta=0`、`route_infrastructure_delta=1`、
  `obstruction_map_delta=1`、`source_assumption_weakening_delta=1`。算术标量界、双 cutoff
  uniform simple-even、真实 ground-state 极限与 RH 继续 open。
- 预注册提交 `47d6adb4d8f25bf3d631cd449159a98eb1b94c20` 已通过公开 Lean Action run
  `29931671154`、build job `88962703883`（`1m55s`）。下一门禁是实现提交及其公开 CI；持续
  RH Goal active。
- implementation commit `21dabbcd2a14c306738af5019924475cde1e5238` 已通过公开 Lean
  Action run `29933348708`、build job `88968461122`（`2m5s`）。Lean 源码冻结；只待
  immutable evidence backfill、其独立公开 CI 与 final-ledger 闭环。
- evidence commit `552c7716673fb2cddd02efc1a1e6a83423a3ef48` 已通过公开 Lean Action
  run `29933695505`、build job `88969645422`（`2m2s`）。本 campaign 在注册的 finite iff
  成功端点停止；只待 final-ledger commit 及其 CI，随后回到跨路线历史选题，不自动停留在
  H7 arithmetic bound 优化。

## 2026-07-22 H7 closure 与 H1 short-mollifier 后继预注册

- H7 final-ledger commit `7e15cfb386e961f7437dfa25d39b6cab85d3946b` 已通过公开 Lean
  Action run `29934044666`、build job `88970856616`（`1m37s`）；finite Herglotz campaign
  完整公开闭合。
- 跨路线比较选择 `LITERATURE-20260722-H1-SHORT-MOLLIFIER-VARIATIONAL-01`，节点
  `H1-SHORT-MOLLIFIER-VARIATIONAL-01`。H2/H11 仍缺单个异常零点 localizer，H10 仍缺数域
  trace 对象；H1 的 2025 来源明确暴露未充分利用的 derivative-combination 自由度。
- 新 campaign 不优化表格小数。它重建 arXiv:2508.11108v1 equations `(58)`-`(63)`，并检查
  `c<1/4` 是否通过带 `cosh` 权的 `1/4` Hardy inequality 保证 Euler-Lagrange 解是整个固定
  端点函数类中的 unique global minimizer。
- 源文的 mean-value asymptotic、超几何公式、Mathematica 结果、临界线比例与 open questions
  均不作为 Lean 前提。预注册公开 CI 通过前不编辑 Lean proof source；持续 RH Goal active。

## 2026-07-22 H1 short-mollifier variational 本地完成

- campaign `LITERATURE-20260722-H1-SHORT-MOLLIFIER-VARIATIONAL-01` 达到固定本地端点，分类为
  `PROVED / KNOWN_ANALYSIS_FORMALIZED / SOURCE_SUFFICIENCY_CERTIFIED`。
- `ShortMollifierVariational.lean` 精确对齐来源 `(58)` 与归一化能量，证明带 `cosh` 权的平方
  完成恒等式与 `1/4` Hardy 界，并由来源加权 Euler-Lagrange 方程导出完整能量差。
- `c<1/4`、`R>0` 与固定端点给出严格二次变分：任一在闭区间某点不同的 C1 competitor 都有
  严格更高能量。因此来源 stationary path 在所表示函数类中是 unique global minimizer；无需
  超几何显式解、Mathematica 或数值比例。
- 374 行生产模块、六条 exact TargetChecks、六项 selected standard-only axiom prints、禁用项
  扫描、`git diff --check` 与全项目 8,740-job build 均通过；选定声明只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。
- `OBS-H1-LONG-MEAN-VALUE-01` 与 `OBS-H1-SPARSE-EXCEPTION-01` 原样开放；本结果不推出新的
  临界线比例、比例一、异常零点排除或 RH。deltas 为 `rh_frontier_delta=0`、
  `hard_gap_delta=0`、`route_infrastructure_delta=1`、`source_sufficiency_audit_delta=1`。
- 下一门禁为 implementation commit 与公开 CI，随后再做 immutable evidence backfill；持续
  RH Goal active，六份受保护用户/曝光文件未被修改或暂存。
- implementation commit `bc1a4004979d12406f2bd415b4a44c6ba6269754` 已通过公开 Lean
  Action run `29936756654`、build job `88980205237`（`2m2s`）。Lean 源码冻结；只待
  immutable evidence backfill、其独立公开 CI 与 final-ledger 闭环。
- evidence commit `e4a45a430170d7398792f18a6e2105109e568aee` 已通过公开 Lean Action
  run `29937092592`、build job `88981336680`（`1m32s`）。本 campaign 在注册的结构充分性
  端点停止；只待 final-ledger commit 及其 CI，随后重新进行跨历史路线价值排序。

## 2026-07-23 H1 closure 与 H9 Conrey rationality-gap 后继预注册

- H1 final-ledger commit `02e8f746a1afacf87d74196883e909f0053a8618` 已通过公开 Lean
  Action run `29937476151`、build job `88982651332`（`2m9s`）；short-mollifier variational
  campaign 完整公开闭合。
- 跨路线比较选择 `FALSIFICATION-20260723-H9-CONREY-RATIONALITY-GAP-01`，节点
  `H9-CONREY-RATIONALITY-FLAT-INTERVAL-01`。H10 的有限谱端点已完成而数域 trace/tail 缺失；
  H2/H11 仍无单异常零点 localizer；ranked D10 是尚未 theorem-producing 试探的最高门。
- Conrey 2024 Proposition 1 从 `A-B/(q*x)=H` 推出 `x` 有理，但该代数步在 `B=0` 时不成立。
  来源稍后自己列出 `A=H,B=0` 的 flat branch，却只称其 unlikely，没有证明排除。
- 新 campaign 将 Lean 证明正确的 flat-or-rational 二分式，并给出 `B=0,A=H,x=sqrt(2)` 的
  generic irrational countermodel。它不声称实际 quadratic-character Proposition 1 已被反驳；
  只有 kernel-checked actual flat prefix 才能支持该结论。
- 预注册与同步台账先单独提交并通过公开 CI；在此之前不编辑 Lean proof source。持续 RH
  Goal active。
- 用户进一步裁定：历史足迹主线的目的，是逐条重建主要人类路线并搜寻被忽略的分支、可弱化
  前提或跨路线输入；在主要家族覆盖完成前默认继续这种 omission audit。只有普查均未找到可行
  修补时，才把主要精力转向原创路线，但原创猜想的提出、反例检验与直接证明尝试始终开放。

## 2026-07-23 H9 Conrey rationality-gap 本地实现完成

- 预注册 commit `7e682226d4ac7965ba0f02265578d1c71dc0d9ad` 已通过公开 Lean Action run
  `29939270138`、build job `88988711235`（`2m3s`）。
- 新模块 `LeanLab/Riemann/ConreyCharacterSumRationality.lean` 编译固定前缀恒等式、零一阶矩
  导致的尺度平坦性、完整 flat-or-rational 二分、有理参数推论和 `sqrt(2)` 反模型。
- 五个 exact TargetChecks 与五个选定 `#print axioms` 通过；后者仅含 `propext`、
  `Classical.choice`、`Quot.sound`。禁用构造扫描为空，`git diff --check` 与完整 `8,741`-job
  build 通过。
- 精确分类为 `SOURCE_GENERIC_INFERENCE_FALSIFIED / ACTUAL_CHARACTER_PROPOSITION_OPEN`：尚未找到
  或假设真实二次特征的 flat prefix，故不声称 Proposition 1 已被反驳。
- 下一闸门为 implementation commit 与公开 CI；此后冻结 Lean proof source。持续 RH Goal active。

## 2026-07-23 H9 Conrey implementation CI 通过

- Implementation commit `4c9939496e6a508c2f5e631ad3fa5ede9f5a69aa` 已通过公开 Lean Action
  run `29940099631`、build job `88991480954`（`1m56s`）。
- 证明源码、Targets、exact checks 与公理审计现冻结于该提交；只回填不可变证据。
- 下一闸门为 evidence commit 与其公开 CI，然后发布最终台账并回到历史路线选择。实际
  quadratic-character flat-prefix 排除与 RH 仍 open；持续 RH Goal active。

## 2026-07-23 H9 Conrey evidence CI 通过并到达局部停止点

- Evidence commit `3f6eee393a262582f3d52a54f5e18bf07e6dd143` 已通过公开 Lean Action
  run `29940351313`、build job `88992322443`（`1m48s`）。
- Campaign 在预注册的 corrected-dichotomy + countermodel 成功端点停止；证明源码继续冻结。
- 未决 source obligation 是对每个实际相关二次特征前缀排除 `B_m=0,A_m=H`，或为
  Proposition 1 提供独立证明。它不是本 campaign 已证明的内容。
- 发布 final ledger 并要求公开 CI 后，持续 RH Goal 进入新的历史路线价值比较。

## 2026-07-23 H9 公开闭合与 H12 Speiser 后继预注册

- H9 final-ledger commit `418a1b3e469a0a71e67ba39ac22eb0dd974d37f3` 已通过公开 Lean
  Action run `29940746044`、build job `88993661951`（`1m30s`）；campaign 完整公开闭合。
- 新 campaign `LITERATURE-20260723-H12-SPEISER-COUNTING-EQUIVALENCE-01` 选择完整 Speiser
  等价重建，因为它正面对应 H1/H2 缺失的 single-exception localizer。
- 来源校正：Speiser 正式卷期为 1935；原 level-curve 证明有已知严谨性空隙，不作为前提。
  主证明脊柱采用 Levinson-Montgomery 1974 Theorem 1 与其 Speiser corollary。
- 关键区分：`N'_-(T)=N_-(T)+O(log T)` 不能排除有限异常；无界高度序列上的 exact count
  equality 才是离散逻辑铰链。Lean 先构造导数 divisor/count consumer，再攻击产生该序列的
  函数方程、边界符号、缩进轮廓与辩值原理步骤。
- 预注册必须先通过公开 CI；此前不编辑 H12 proof source。持续 RH Goal active。

## 2026-07-23 H12 Speiser 计数消费器本地完成

- 预注册 commit `178d86eaa7d02d8eb88421171bee8964c722fb0e` 已通过公开 Lean Action run
  `29941747166`、build job `88997067033`（`1m33s`）。
- 新模块 `LeanLab/Riemann/SpeiserCountingEquivalence.lean` 共 465 行：构造实际 `zeta'`
  divisor、上左开矩形内的 zeta/导数有限乘数计数，并编译 exact-count last-exception
  consumer。
- 跨路线复用 H6 的虚轴严格正性与 `H_0`--xi 坐标，Lean 已无条件排除临界带实轴上的
  非平凡 zeta 零点，因此正高度计数可以接回 mathlib 的全局 RH 定义。
- 来源逻辑校正：Levinson-Montgomery 不是无条件给出 exact sequence，而是给出
  exact-or-eventually-`N_-(T)>T/2` 二分和 `O(log T)` 计数差。Lean 已证明 `O(log T)`
  形式蕴含所需次线性界，并证明这两个来源输出足以推出完整 Speiser 等价。
- 本轮分类为 `MEANINGFUL_PARTIAL / CONDITIONAL_SOURCE_CONSUMER`，不是完整 Speiser 定理。
  首个精确外部解析障碍是为实际计数证明 `LevinsonMontgomeryLogCountBound` 与
  `LevinsonMontgomeryCountDichotomy`，涉及缩进轮廓、函数方程零点和、Gamma 估计及辩值原理。
- 五项 TargetChecks、五项标准公理审计通过；全量 8,742-job build 通过。implementation
  commit 与公开 CI 是下一闸门；持续 RH Goal active。

## 2026-07-23 H12 Speiser implementation CI 通过

- 冻结的实现 commit `2a6290a27fd7675db409f884679d1a554c13b72d` 已通过公开 Lean Action
  run `29943873685`、build job `89004249306`（`2m6s`）。
- 该提交独立重建了 465 行 production module、Targets、五项 TargetChecks 与五项公理审计；
  没有把 `LevinsonMontgomeryLogCountBound` 或 `LevinsonMontgomeryCountDichotomy` 当作已证明结论。
- Lean 证明源码现冻结。下一步仅提交不可变实现证据并要求其独立 CI；随后写最终台账，结束
  本地 H12 consumer campaign 并返回历史路线遗漏搜索。H12-D/H12-E 与 RH 保持 open。
- 六个继承保护文件继续未触碰、未暂存；持续 RH Goal active。

## 2026-07-23 H12 Speiser evidence CI 通过

- 不可变证据 commit `eeca9f7fc910b323df7aaaec00f3258c92063483` 已通过公开 Lean Action
  run `29944285692`、build job `89005620974`（`1m33s`）。
- H12 consumer 的预注册、冻结实现和证据提交现均可公开复现；本轮局部分类保持
  `MEANINGFUL_PARTIAL / CONDITIONAL_SOURCE_CONSUMER`，不是 Speiser 定理完成。
- 最终台账 CI 后返回跨家族历史路线遗漏搜索。H12-D/H12-E 留在 open 障碍图，可在其解析
  先决条件价值高于其他路线时重启；原创猜想和直接攻击 RH 始终开放。
- 六个继承保护文件继续未触碰、未暂存；持续 RH Goal active。

## 2026-07-23 H12 闭合与 H11 对关联路线启动

- H12 最终台账 commit `100bc02d691b6a69cf2ca903f8a0aa9f6c99dca1` 已通过公开 Lean Action
  run `29944572919`、build job `89006584781`（`2m26s`）；consumer campaign 已公开闭合，
  H12-D/H12-E 仍 open。
- 跨家族检索发现门径图遗漏了 arXiv:2503.15449v4（2026-03-30 修订）：作者在不假定 RH
  的情况下证明 PCC 蕴含渐近 100% 的零点简单且位于临界线，并明确修正旧文“对关联不提供
  水平信息”的说法。
- 新机制是水平重数：离线零点与 `1-conj(rho)` 具有同一高度，会产生额外对角项；但
  `N_circ/N -> 1` 仍容许有限或密度零的离线例外，所以该来源没有证明 RH。
- 已本地预注册 `LITERATURE-20260723-H11-PCC-HORIZONTAL-MULTIPLICITY-01`：Lean 将重建有限
  计数不等式、精确计数的最后例外消费器，以及“固定一对离线零点但比例趋一”的反模型，
  随后尝试实际 zeta 乘数计数适配。预注册公开 CI 前不编辑证明源码。
- 六个继承保护文件继续未触碰、未暂存；持续 RH Goal active。

## 2026-07-23 H11 对关联横向重数本地实现完成

- 预注册 commit `10c016f9395b7bd3c2c2d4e99c4148471540f31f` 已通过公开 Lean Action
  run `29945736404`、build job `89010521220`（`1m35s`），此后才开始编辑证明源码。
- 新模块 `LeanLab/Riemann/PairCorrelationHorizontalMultiplicity.lean` 完成来源有限计数铰链：
  在同高度函数方程反射下，Lean 证明 `2*N <= N_simple_critical + N_circ`，并证明
  `N_circ=N` 会强制所有横向纤维为单点且位于临界线。
- 反证轨道构造一对永久离线反射点和 `n` 个简单临界线点：总数 `n+2`、横向对数
  `n+4`、简单临界数 `n`，两个归一化比例都趋于 `1`，但每个 `n` 仍有离线点。因此
  “密度一推出 RH”不能从反射与归一化计数本身得到。
- 实际 zeta 适配已编译：有限正高度非平凡零点、解析重数副本、函数方程反射置换均已构造；
  并通过局部非零解析单位证明 zeta 零点重数等于项目 xi 重数。
- 条件定理 `PccExactHorizontalPairCountCofinal -> RiemannHypothesis` 已编译，但前件未证明，
  PCC 也未作为前提加入。真正开放的 H11 缺口是从一个实际离线轨道推出 PCC 可见的非稀疏
  横向超额，或以其他方法证明 exact cofinal equality。
- 六条 exact TargetChecks 与六项 selected axiom audit 通过；选定定理只依赖 `propext`、
  `Classical.choice`、`Quot.sound`。定义对齐见
  `research/h11_pair_correlation_definition_alignment_20260723.md`。
- 禁用构造扫描为空，`git diff --check` 通过，H11 模块自身无新增 warning，全量 `8,743`-job
  build 通过。下一闸门是 implementation commit 与公开 CI。分类为
  `FULL_SUCCESS_AT_REGISTERED_ENDPOINT / rh_frontier_delta=0 / route_infrastructure_delta=1`；
  持续 RH Goal active。

## 2026-07-23 H11 implementation CI 通过

- 冻结实现 commit `a2c8dc06f493f8577de668286482c4cbe2e6498f` 已通过公开 Lean Action
  run `29948610437`、build job `89020321751`（`2m1s`）。
- 公开 runner 独立重建了 H11 生产模块、Targets、六条 exact TargetChecks 与六项公理审计；
  没有把 PCC、exact cofinal equality、稀疏例外放大或 RH 标成已证明。
- Lean 证明源码现冻结。下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后
  发布最终台账并返回历史路线遗漏搜索。持续 RH Goal active。

## 2026-07-23 H11 evidence CI 通过并到达局部停止点

- 不可变证据 commit `3a2d721d0397ff40c9bce496149ac1e05b84db6c` 已通过公开 Lean Action
  run `29948908677`、build job `89021336009`（`2m10s`）。
- 预注册、冻结实现和不可变证据现均可公开复现；证明源码继续冻结。
- 本 campaign 在注册的有限计数铰链、条件 exact consumer 与稀疏例外反模型端点停止。
  H11-D 的 PCC 解析输入、H11-E 的算术稀疏例外放大和 RH 全部保持 open。
- 发布 final ledger 并要求其公开 CI 后，持续 RH Goal 立即返回跨家族历史路线遗漏搜索；
  原创猜想和直接证明尝试仍始终开放。

## 2026-07-23 H11 公开闭合

- Final-ledger commit `3424cb661487a45e544eb4fa1ff4ad8bcd757455` 已通过公开 Lean
  Action run `29949249815`、build job `89022493860`（`1m33s`）。
- H11 有限计数/条件消费器/反模型 campaign 完整公开闭合；H11-D 的 PCC 解析输入、H11-E 的
  稀疏例外算术放大以及 RH 仍为 open。
- 持续 RH Goal 已返回跨家族历史路线遗漏搜索；下一候选优先补尚未 theorem-producing 的
  H8 Jensen/Laguerre--Polya 路线，而非继续优化 H11 的比例或常数。

## 2026-07-23 H8 Jensen eventual-hyperbolicity 预注册

- 跨家族比较没有选择 H2：其“密度允许有限/稀疏例外”的逻辑已由 H11 参数反模型精确覆盖，
  当前没有新的单例外 localizer。H7 也已有三次连续有限谱 campaign，下一步是算术统一界或
  无限 ground-state 极限，不宜立刻重复。
- 新 campaign `FALSIFICATION-20260723-H8-JENSEN-EVENTUAL-HYPERBOLICITY-01` 补 H8 这一尚未
  theorem-producing 的历史家族。来源检索未发现 2025--2026 的全次数/全位移统一机制。
- 新增来源遗漏：Durán 2024 把 Jensen--Pólya--Schur 推广到 Brenke 多项式并给出更多 RH
  等价实根判据，但没有证明 all-index 条件，因此按“新等价重述”登记，不当作 RH 进展。
- Lean 固定端点是一个单系数缺陷族：任意给定的有限初始 Jensen 检查都与全一系数模型相同，
  每个固定次数最终也都只有实根，但某个二次窗口严格等于 `1+X^2` 并有非实根 `I`。
- 该模型不是 xi 系数，不反驳来源定理；它只反证从 finite/eventual fixed-degree 到
  all-degree/all-shift 的升级。预注册公开 CI 前不编辑 H8 proof source；持续 RH Goal active。

## 2026-07-23 H8 Jensen 反模型本地实现完成

- 预注册 commit `0275ab15b83a253b9a4eb9fcfa4a575943b89b33` 已通过公开 Lean Action
  run `29949869070`、build job `89024569873`（`1m54s`），之后才编辑 H8 proof source。
- 新模块 `LeanLab/Riemann/JensenEventualHyperbolicity.lean` 定义精确 Jensen 系数窗口与复根
  实轴谓词，并证明窗口只依赖 `a(n),...,a(n+d)`。
- 单缺陷序列在缺陷前任意有限楔形和缺陷后所有充分大位移都严格给出 `(1+X)^d`；因此每个
  固定次数最终实根。但跨过缺陷的二次窗口严格为 `1+X^2`，Lean 以 `I` 证明存在非实根。
- 组合定理正式反证 generic implication
  `forall d, eventually n -> forall d n`；该序列不是 xi 系数，因此不反驳来源定理或
  Jensen--Polya 等价，也不改变 RH 前沿。
- 两个 Targets、七条 exact TargetChecks 与六项 selected axiom audit 通过；选定定理只依赖
  `propext`、`Classical.choice`、`Quot.sound`。定义对齐见
  `research/h8_jensen_eventual_hyperbolicity_definition_alignment_20260723.md`。
- 禁用构造扫描为空，`git diff --check` 通过，H8 模块自身无新增 warning，全量 `8,744`-job
  build 通过。下一闸门是 implementation commit 与公开 CI；持续 RH Goal active。

## 2026-07-23 H8 Jensen implementation CI 通过

- 冻结实现 commit `ca656cb6e24b5084b403d53e5a3763dc34b642be` 已通过公开 Lean Action
  run `29950744385`、build job `89027520728`（`2m4s`）。
- 公开 runner 独立重建了 H8 生产模块、两个 Targets、七条 exact TargetChecks 与六项公理
  审计；未把 generic 单缺陷序列认作 xi 系数，也未把 actual-xi all-index hyperbolicity 或 RH
  标成已证明。
- Lean 证明源码现冻结。下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后
  发布最终台账并返回跨家族历史路线遗漏搜索。原创猜想和直接 RH 攻击始终开放，持续 RH
  Goal active。

## 2026-07-23 H8 Jensen evidence CI 通过并到达局部停止点

- 不可变证据 commit `c567b96b0315121c3df10c4088422121f8f866a9` 已通过公开 Lean Action
  run `29951025462`、build job `89028448900`（`1m37s`）。
- 预注册、冻结实现与不可变证据现均可公开复现；Lean 证明源码继续冻结。
- 本 campaign 在“固定次数最终实根不推出全次数/全位移实根”的 generic 反模型端点停止。
  actual-xi all-index hyperbolicity、Jensen 路线和 RH 均保持 open。
- 发布 final ledger 并要求其公开 CI 后，持续 RH Goal 返回跨家族历史路线遗漏搜索；原创猜想
  和直接 RH 攻击仍始终开放。

## 2026-07-23 H8 公开闭合并启动 D9 Suzuki 极限审计

- H8 final-ledger commit `c80b9e6a4114d7d591f4db72e6326810d0fe9d1c` 已通过公开 Lean
  Action run `29951256366`、build job `89029220136`（`1m53s`）。generic 量词反模型 campaign
  完整闭合；actual-xi all-index hyperbolicity 与 RH 保持 open。
- 历史广度比较选择尚无 theorem-producing campaign 的 D9 de Branges/canonical-system 门。
  新增一手来源 Suzuki 2026：每个有限区间的自伴扩张特征函数无条件只有实零点，但到
  `z^2*xi/xi'` 的无限区间紧一致极限仍是猜想。
- 原文显示的 Corollary 6 没有写出归一化指数 `phi` 的解析性。若按字面有限值读取，实零点
  不能只凭一致收敛传递；若补成整函数归一化，极限必须为整函数，而倒数对数导数在非零
  临界点可能有不可去极点。meromorphic 解释需要另立拓扑与零点传递定理。
- 已预注册 `FALSIFICATION-20260723-D9-SUZUKI-RECIPROCAL-LIMIT-01`，固定两个 generic Lean
  证人：单点穿孔的一致极限反模型，以及具有非零导数临界点的对称实根四次模型。它们不
  冒充 source `W` 或 actual xi；预注册公开 CI 前不编辑证明源码。持续 RH Goal active。

## 2026-07-23 D9 Suzuki 正规性审计本地实现完成

- 预注册 commit `b455391bf7211e0136a98b082f1264fee4cac1ca` 已通过公开 Lean Action run
  `29952313617`、build job `89032753680`（`1m54s`），之后才开始编辑证明源码。
- 新模块 `LeanLab/Riemann/SuzukiReciprocalLogDerivativeAudit.lean` 证明穿孔函数列处处无零点，
  并以标准 `TendstoUniformlyOn` 谓词在任意集合上一致收敛到具有非实零点 `I` 的 `z-I`。
  取 `W_n=1`、`phi_n=log(punctured_n)` 后，Lean 精确证明
  `exp(phi_n)*W_n=punctured_n`，从而反证不含正规性条件的 generic 零点传递 schema。
- 同一模块证明对称实根四次函数
  `(z^2-(1/5)^2)*(z^2-(7/5)^2)` 的导数为 `4*z^3-4*z`；在非零点 `z=1`，导数为零而
  函数非零，因此不存在全平面有限值 `F` 满足 `f'*F=z^2*f`。
- 两个反模型都不是 source `W` 或 actual xi。它们只裁定字面有限值解释和普遍有限整函数
  延拓解释；meromorphic 拓扑、实际 canonical-system 极限及 RH 全部保持 open。
- 两个 Targets、九条 exact TargetChecks、七项 selected axiom audit 已编译；所选定理只依赖
  `propext`、`Classical.choice`、`Quot.sound`。定义对齐见
  `research/d9_suzuki_reciprocal_log_derivative_definition_alignment_20260723.md`。
- 下一闸门是禁用构造扫描、diff 检查、全量 build，然后发布 implementation commit 并要求
  公开 CI。六个受保护文件保持未触碰、未暂存；持续 RH Goal active。

## 2026-07-23 D9 Suzuki implementation CI 通过

- 冻结实现 commit `8442a4ac2b71886efbc11fb90d78a91a8cbdbcdb` 已通过公开 Lean Action
  run `29954158019`、build job `89038905667`（`2m37s`）。
- 公开 runner 独立重建了 D9 生产模块、两个 Targets、九条 exact TargetChecks 与七项公理
  审计；没有把 generic 正规性反模型认作 source `W`、actual xi 或 RH 结论。
- Lean 证明源码现冻结。下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后
  发布最终台账并返回尚未完成的历史路线遗漏搜索。实际 canonical-system 极限、meromorphic
  修补、原创猜想与直接 RH 攻击均保持 open；持续 RH Goal active。

## 2026-07-23 D9 Suzuki evidence CI 通过并到达局部停止点

- 不可变证据 commit `36d6f6e9b47240e95b9d6668d7a4cc9bccc8045e` 已通过公开 Lean
  Action run `29954848710`、build job `89041187831`（`1m32s`）。
- 预注册、冻结实现与不可变证据现均可公开复现；Lean 证明源码继续冻结。
- 本 campaign 在两个 generic 解释审计端点停止：缺少正规性的有限值归一化不支持零点传递，
  非零临界点可阻止全平面有限值倒数对数导数延拓。实际 Suzuki 算子极限、meromorphic 修补、
  D9 路线和 RH 均保持 open。
- 发布 final ledger 并要求其公开 CI 后，持续 RH Goal 返回未完成的历史路线遗漏搜索；原创猜想
  和直接 RH 攻击仍始终开放。

## 2026-07-23 D9 公开闭合并启动 H10 无限普通迹审计

- D9 final-ledger commit `276282262f033aeb3f106e7eb66180a92b23ec4d` 已通过公开 Lean
  Action run `29955117117`、build job `89042095525`（`2m2s`）。generic 正规性审计完整闭合；
  actual Suzuki canonical-system 极限、meromorphic 修补与 RH 保持 open。
- 新一轮历史广度选择转向函数域类比。有限 Frobenius 谱的普通幂和刚性已经编译，但尚未测试
  它能否连同非零倒数配对一起直接搬到可数无限谱。
- 已预注册 `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01`：若某个正次数幂列
  `alpha(n)^k` 可普通求和，则它及置换重排都趋于零；而固定倒数配对会让两者乘积恒等于
  `q^k`。目标是由此证明非零 `q` 与这种 ordinary trace 不相容，并另给有限谱反例说明障碍
  确实来自无限转移。
- 该审计不把 `alpha` 冒充 zeta 零点，不排除 regularized/distributional trace，也不关闭
  Hilbert-Polya、Connes 路线或 H10。预注册公开 CI 前不编辑证明源码；六个受保护文件保持
  未触碰、未暂存，持续 RH Goal active。

## 2026-07-23 H10 无限普通迹审计本地实现完成

- 预注册 commit `8077a2558142a1968b283296e9fc196da02bda93` 已通过公开 Lean Action
  run `29955908591`、build job `89044796394`（`2m32s`），之后才开始编辑证明源码。
- 新模块 `LeanLab/Riemann/InfiniteReciprocalTraceAudit.lean` 证明：若正整数 `k` 的普通幂迹
  `Summable (alpha(n)^k)` 成立，则原序列和任意置换重排都趋于零；若同时
  `alpha(sigma(n))*alpha(n)=q`，则极限唯一性迫使 `q^k=0`，从而 `q=0`。
- 因此非零固定倒数配对排除每个正次数 ordinary power trace。`Fin 1` 上 `alpha=1,q=1`
  的精确见证则说明有限谱完全可以同时拥有倒数配对和全部幂迹。
- 该结论只关闭“把有限 Frobenius 普通幂和原样搬到可数无限谱”的 generic 方案；不涉及 zeta
  零点，不排除 regularized/distributional trace、Hilbert-Polya、Connes 路线或 RH。
- 两个 Targets、七条 exact TargetChecks、七项 selected axiom audit 已编译；所选定理只依赖
  `propext`、`Classical.choice`、`Quot.sound`。定义对齐见
  `research/h10_infinite_reciprocal_trace_definition_alignment_20260723.md`。
- 下一闸门是禁用构造扫描、diff 检查、全量 build，然后发布 implementation commit 并要求
  公开 CI。六个受保护文件保持未触碰、未暂存；持续 RH Goal active。

## 2026-07-23 H10 无限普通迹 implementation CI 通过

- 冻结实现 commit `34b307baaca52e043d05668894abe4cceb9a3c2a` 已通过公开 Lean Action
  run `29956666496`、build job `89047355398`（`2m25s`）。
- 公开 runner 独立重建了 H10 生产模块、两个 Targets、七条 exact TargetChecks 与七项公理
  审计；该结论仍严格限于普通 `Summable` 幂迹，没有冒充正则化迹、zeta 谱构造或 RH 结论。
- Lean 证明源码现冻结。下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后
  发布最终台账并返回尚未完成的历史路线遗漏搜索。regularized/distributional trace、实际
  数域谱对象、原创猜想与直接 RH 攻击均保持 open；持续 RH Goal active。

## 2026-07-23 H10 无限普通迹 evidence CI 通过并到达局部停止点

- 不可变证据 commit `332616ce1d8e0cca4824ef63f135283e9f45b0b3` 已通过公开 Lean
  Action run `29957075006`、build job `89048714221`（`2m4s`）。
- 预注册、冻结实现与不可变证据现均可公开复现；Lean 证明源码继续冻结。
- 本 campaign 只在 H10-C 的字面 ordinary-summability 端点停止：非零固定倒数配对不能与
  任一正次数普通幂迹同时成立。regularized/distributional trace、实际数域 zeta 谱对象、
  H10 路线和 RH 均保持 open。
- 发布 final ledger 并要求其公开 CI 后，持续 RH Goal 返回未完成的历史路线遗漏搜索；原创猜想
  和直接 RH 攻击仍始终开放。

## 2026-07-23 H10 公开闭合并启动 H2 半孤立 bow 几何审计

- H10-C final-ledger commit `2edf069a217255bbc20b93a2aa938f51dd57d94e` 已通过公开 Lean
  Action run `29957374602`、build job `89049724940`（`1m54s`）。普通可求和无限迹审计完整
  闭合；regularized/distributional trace、H10 与 RH 保持 open。
- 历史覆盖比较选择 canonical H2，而不是继续优化普通迹或某个密度指数。H1、H7/H8、H10、
  H11 已有 theorem-producing campaign；H2 尚无独立 attempt。
- 一手来源审计发现原 atlas 漏掉 Maynard--Pratt 的 half-isolated-zero 分支。该方法利用零点
  纵向几何；有限固定竖线假设能给簇的底部半孤立零点，而论文明确把缓慢弯曲的 bow 配置
  识别为去除这项刚性的障碍。
- 已预注册 `FALSIFICATION-20260723-H2-HALF-ISOLATED-BOW-01`：Lean 将证明离散竖线间隔下
  的 rightmost-bottom 正结论，并尝试一个临界线反射不变、含离线点但右侧无半孤立点的有限
  bow。它不冒充 actual zeta 零集，不证明解析 detector、零密度或 RH。
- 预注册公开 CI 前不编辑 Lean 证明源码；六个受保护文件保持未触碰、未暂存，持续 RH Goal
  active。原创猜想和直接 RH 攻击仍始终开放。

## 2026-07-23 H2 半孤立 bow 几何审计本地实现完成

- 预注册 commit `1475d90b96f6a5aabf9a6afea72a56575f11dc61` 已通过公开 Lean Action
  run `29958359541`、build job `89053021275`（`1m48s`），之后才开始编辑证明源码。
- 新模块 `LeanLab/Riemann/HalfIsolatedBowAudit.lean` 精确保留 half-isolated 定义的两个分支。
  Lean 证明：离散竖线间隔加 rightmost-bottom 极值足以推出完整半孤立条件。
- 同一模块给出非真空的有限三点 bow：集合在 `rho |-> 1-star(rho)` 下不变，含右侧离线点，
  但附近较低 blocker 的实部位移严格夹在两个阈值之间，因此所有右侧离线点都不半孤立。
- 这只否定“函数方程反射对称可替代有限实部刚性”的 generic 提升，不说明 actual zeta bow
  存在。解析 short detector、actual bow exclusion、零密度估计、H2 与 RH 全部保持 open。
- 两个 Targets、七条 exact TargetChecks、六项 selected axiom audit 已编译；所选声明只依赖
  `propext`、`Classical.choice`、`Quot.sound`。定义对齐见
  `research/h2_half_isolated_bow_definition_alignment_20260723.md`。
- 下一闸门是禁用构造扫描、diff 检查、全量 build，然后发布 implementation commit 并要求
  公开 CI。六个受保护文件保持未触碰、未暂存；持续 RH Goal active。

## 2026-07-23 H2 半孤立 bow implementation CI 通过

- 冻结实现 commit `2cac0b4813435dffe468cd87f888d9f2763263d9` 已通过公开 Lean Action
  run `29959216007`、build job `89055884594`（`2m11s`）。
- 公开 runner 独立重建了 H2 生产模块、两个 Targets、七条 exact TargetChecks 与六项公理
  审计；没有把有限 bow 认作 actual zeta 零集或 bow 存在性结论。
- Lean 证明源码现冻结。下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后
  发布最终台账并返回尚未完成的历史路线遗漏搜索。解析 detector、actual bow exclusion、
  零密度估计、原创猜想与直接 RH 攻击均保持 open；持续 RH Goal active。

## 2026-07-23 H2 半孤立 bow evidence CI 通过并到达局部停止点

- 不可变证据 commit `5f9f8ea175c269507e96fbb0a8ca8dff40144e12` 已通过公开 Lean
  Action run `29959619394`、build job `89057229832`（`1m30s`）。
- 预注册、冻结实现与不可变证据现均可公开复现；Lean 证明源码继续冻结。
- 本 campaign 只在 finite-line-versus-symmetry generic 几何端点停止：竖线离散性足以产生
  半孤立点，反射对称本身不足。解析 detector、actual-zeta bow exclusion、H2 与 RH 保持 open。
- 发布 final ledger 并要求其公开 CI 后，持续 RH Goal 返回未完成的历史路线遗漏搜索；原创猜想
  和直接 RH 攻击仍始终开放。

## 2026-07-23 H2 公开闭合并启动 H13 Dirichlet-family inclusion 审计

- H2 final-ledger commit `b13bc623e266990e9ba40802c6e1deb5ed87215a` 已通过公开 Lean
  Action run `29959903737`、build job `89058172229`（`2m14s`）。finite-line-versus-symmetry
  generic 几何审计完整闭合；解析 detector、actual-zeta bow exclusion、H2 与 RH 保持 open。
- 历史覆盖比较转向 H13，这是 source-aligned 但尚无独立 theorem-producing campaign 的路线；
  H14 仍是 supporting finite computation。此次不回到密度指数或常数优化。
- Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` 的真实 Dirichlet L-function
  接口证明模 1 的唯一成员逐点等于 `riemannZeta`。已预注册
  `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01`，核验模 1 critical-strip claim
  与 RH 的精确等价，以及 all-Dirichlet family claim 到 RH 的特化。
- 同一 campaign 将核验 zeta-factor 的单向传递，并用带显式离线根的附加因子否定反向等价的
  自动提升。该反例不冒充 Davenport--Heilbronn、Dedekind、Rankin--Selberg 或 p-adic
  L-function；不证明 generalized RH、H13 或 RH。
- 预注册公开 CI 前不编辑 Lean 证明源码；六个受保护文件保持未触碰、未暂存，持续 RH Goal
  active。原创猜想和直接 RH 攻击仍始终开放。

预注册 commit `e001e3afb37818918e42b08d76c18b6490062ac7` 已通过公开 Lean Action run
`29960700375`、build job `89060685988`（`2m2s`）。proof-source gate 已打开；实现必须保持模 1
精确等价、all-family 单向特化、zeta-factor 单向传递和附加因子反例四个边界不变。

## 2026-07-23 H13 Dirichlet-family inclusion 本地实现完成

- 新模块 `LeanLab/Riemann/DirichletFamilyInclusionAudit.lean` 证明：开临界带内的 zeta 零点
  全在临界线与 Mathlib RH 精确等价；模 1 的 Dirichlet L-function 版本因此也精确等价于 RH。
- all-Dirichlet family claim 只能通过模 1 成员推出 RH；任意 `zeta*g` 的临界带零点全在线也
  单向推出 RH。反向不自动成立，因为因子 `s-1/4` 在带内加入精确离线零点。
- 该 generic 因子不冒充 Davenport--Heilbronn、Dedekind、Rankin--Selberg、automorphic 或
  p-adic L-function。generalized RH、真实 individual-zeta transfer、H13 与 RH 全部保持 open。
- 一个 proven Target、一个 in-progress Target、八条 exact TargetChecks 和七项 selected axiom
  audit 已通过；七项均只依赖 `propext`、`Classical.choice`、`Quot.sound`。生产禁用构造扫描为空，
  全量 `8,748`-job build 通过，只有既有 replay warnings。
- 定义对齐见 `research/h13_dirichlet_family_inclusion_definition_alignment_20260723.md`。下一闸门
  是发布 implementation commit 并要求公开 CI；六个受保护文件保持未触碰、未暂存，持续 RH
  Goal active。

## 2026-07-23 H13 Dirichlet-family inclusion implementation CI 通过

- 冻结实现 commit `ab45b1bd8ba5c8cdbe5fb2bd9cd87c222131bb91` 已通过公开 Lean Action
  run `29961388807`、build job `89062966415`（`2m18s`）。
- 公开 runner 独立重建了 105 行生产模块、一个 proven 与一个 open Target、八条 exact
  TargetChecks 和七项 standard-only 公理审计。
- Lean 证明源码现冻结。下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后
  发布最终台账并返回历史图谱。generalized RH、真实 automorphic/p-adic individual-zeta
  transfer、H13、原创猜想和直接 RH 攻击均保持 open；持续 RH Goal active。

## 2026-07-23 H13 Dirichlet-family inclusion evidence CI 通过并到达局部停止点

- 不可变证据 commit `cb19d46bd1b62eb15dbd2ff41efe5ddf820c4505` 已通过公开 Lean Action
  run `29961677975`、build job `89063888150`（`2m17s`）。
- 预注册、冻结实现与不可变证据均可公开复现；Lean 证明源码继续冻结。
- 本 campaign 只在 exact family inclusion / product directionality 端点停止。generalized RH、
  actual automorphic/p-adic individual-zeta transfer、H13 与 RH 保持 open。
- 发布 final ledger 并要求其公开 CI 后，持续 RH Goal 返回未完成的历史路线遗漏搜索；原创猜想
  和直接 RH 攻击仍始终开放。

## 2026-07-23 H13 公开闭合并启动 H14 finite-height promotion 审计

- H13 final-ledger commit `11822e34ad720b9715f7cc22d17e2ed066e51803` 已通过公开 Lean
  Action run `29961935426`、build job `89064730187`（`2m17s`）。exact inclusion / product
  directionality campaign 完整闭合；generalized RH、真实 individual-zeta transfer、H13 与 RH
  保持 open。
- 历史覆盖转向最后一个尚无独立 campaign 的 supporting H14。H11 已覆盖 density-one 稀疏例外，
  H8 已覆盖 eventual-index 推广，但都没有 H14 的任意有限高度量词与两项 zeta 基本对称性。
- 已预注册 `FALSIFICATION-20260723-H14-FINITE-HEIGHT-PROMOTION-01`：对每个 `T >= 0`，构造
  有限开临界带对称轨道，使高度 `T` 以下的点全在线，同时保留高度严格大于 `T` 的离线点。
- 该 generic witness 不冒充 actual zeta zero set，不质疑 Platt--Trudgian 认证，也不否定有限
  计算与独立全局解析归约的合法组合；不优化任何数值界。
- 预注册公开 CI 前不编辑 Lean 证明源码；六个受保护文件保持未触碰、未暂存，持续 RH Goal
  active。原创猜想和直接 RH 攻击仍始终开放。

预注册 commit `39ba83974d338cffc563945be9a829d0f73018ba` 已通过公开 Lean Action run
`29962435935`、build job `89066333032`（`1m54s`）。proof-source gate 已打开；实现必须保持任意
非负高度、两项基本对称性、开临界带和严格高处离线 witness 四个边界不变。

## 2026-07-23 H14 finite-height promotion 本地实现完成

- `LeanLab/Riemann/FiniteHeightPromotionAudit.lean`（127 行）已实现固定端点：任意 `T >= 0`
  都存在有限非空开临界带轨道，在共轭和 `rho |-> 1-rho` 下闭合，通过高度 `T` 以下的临界线
  检查，同时包含高度严格大于 `T` 的离线点。
- 关键等式是轨道中每一点都满足 `abs rho.im = T+1`；因此有限核验谓词成立，但不提供任何关于
  高处点的结论。该轨道不是 zeta 零点集，不带 Euler product、显式公式或 Turing 计数结构。
- 两个 Targets 已登记：generic promotion boundary 为 proven，actual-zeta global tail reduction
  仍 open。十项 exact TargetChecks、八项公理打印、production forbidden scan、direct compile 与
  `8,749`-job full build 均通过；公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
- 定义对齐见 `research/h14_finite_height_promotion_definition_alignment_20260723.md`。本地增量为
  `hard_gap_delta=0`、`route_map_delta=1`、`obstruction_map_delta=1`、`rh_frontier_delta=0`。
- 下一门禁是冻结实现提交并要求公开 Lean Action CI。六个受保护文件保持未触碰、未暂存；持续
  RH Goal active，原创猜想和直接 RH 攻击始终开放。
- implementation commit `8c61ef5d87ecf9ba5ffb923dabada87080b89f81` 已通过公开 Lean
  Action run `29963329369`、build job `89069216973`（`2m42s`）。Lean 源码冻结；只待
  immutable evidence backfill、其独立公开 CI 与 final-ledger 闭环。
- immutable-evidence commit `0931f90f08905c0609854788725d151d4ace9632` 已通过公开 Lean
  Action run `29963630200`、build job `89070175938`（`1m34s`）。本 campaign 在注册的 generic
  finite-height promotion endpoint 停止；仅待 final-ledger commit 及其 CI。actual-zeta global
  tail reduction、H14 支持工具、RH、原创猜想和直接攻击保持 open。

## 2026-07-23 H14 公开闭合并启动 H7 prolate Rayleigh-gap 猜想

- H14 final-ledger commit `cd67e4ad4f899631b11b8d6a8927c5709e4f9fa3` 已通过公开 Lean
  Action run `29963802981`、build job `89070709361`（`1m57s`）。generic finite-height promotion
  审计完整闭合；actual-zeta global tail reduction、H14 支持用途与 RH 保持 open。
- H0-H14 campaign coverage 只作为普查基线，不视为人类路线已经穷尽。跨路线比较后重入 H7，
  但不继续优化 finite Herglotz 常数，而是攻击 2025-2026 原始文献明确留下的真实基态
  `xi_lambda` 与显式 prolate 近似 `k_lambda` 的比较。
- 新猜想：真实 source arithmetic matrix 上，归一化 prolate 向量的 Rayleigh excess 除以
  certified ground-state gap，在来源指定的双参数极限中趋零。该猜想为模型原创、未证明、不可
  作为 premise；原文只留下“sufficiently good approximation”，没有给出此比率机制。
- 预注册 campaign `DISCOVERY-20260723-H7-PROLATE-RAYLEIGH-GAP-01`。固定 Lean 端点先证明该
  比率控制到 ground line 的 projective distance，并证明 gap 塌缩时 absolute excess 趋零仍可
  与 defect 恒为 1 共存。actual prime/digamma entries 与 prolate coefficients 尚未实例化，generic
  成功不算 RH 进展。
- 预注册公开 CI 前不编辑新的 Lean 证明源码；六个受保护文件保持未触碰、未暂存，持续 RH Goal
  active。H1/H2/H11 的 last-exception amplifier、直接 RH 与其他原创猜想仍保持开放。

## 2026-07-23 H7 prolate Rayleigh-gap 本地实现完成

- 预注册 commit `38d57244841b2afec22a77b4ffeb07ce51db018a` 已通过公开 Lean Action
  run `29964304967`、build job `89072278256`（`1m37s`），随后才创建证明源码。
- 新模块 `LeanLab/Riemann/WeilGroundStateRayleighGap.lean` 已无警告编译。对有限实对称矩阵，
  归一化基态和正的正交补谱隙证书推出 `delta * projectiveDefect <= rayleighExcess`，并得到
  除法形式与序列 squeeze 消费者。
- 精确二维族 `diag(0,epsilon_n)` 证明：absolute Rayleigh excess 可以趋零，而 projective
  defect 与 excess/gap 都恒为 1。因此真实 prolate 比较必须控制相对谱隙误差，或另证统一正谱隙。
- 一个 generic Target 标记 proven；真实 arithmetic Weil matrix/prolate 双极限比值 Target 保持
  in-progress、没有 `leanName`、不可作为 premise。十二条 exact TargetChecks 与十一项 selected axiom
  prints 通过，公理只有 `propext`、`Classical.choice`、`Quot.sound`。
- 定义对齐见 `research/h7_prolate_rayleigh_gap_definition_alignment_20260723.md`。source entries、
  双极限次序、基态符号定向、transform convergence、real-zero transfer 与 RH 均保持 open。
- production forbidden scan 与 `git diff --check` 为空，direct compiles 通过，全量 `8,750`-job
  build 通过且只有既有 replay warnings。下一门禁是发布冻结 implementation commit 并要求公开
  CI。六个受保护文件保持未触碰、未暂存；持续 RH Goal active。

## Arch 审计第十轮（2026-07-23，Claude）
- 门户普查指令执行到位：Boyd 上界线已冻结，交付 889 行 ranked door atlas（D1-D11），排序规则严格遵循"精确缺失对象+障碍有效性+未用机器"而非易开工度。#1=D6 谱/迹+有限素数 Weil 基态，#2=D3 mollifier，D1 建议并入 D6 不再造新等价判据，D8 Jensen 通用提升已被自证伪。
- 普查后系统开门审计（Jensen/PCC/Speiser/Suzuki/bow/Dirichlet/finite-height），多为障碍与证伪产出。当前跑 D6 支线 H7 prolate Rayleigh gap。
- build 8750 全过；公理审计 745 条零非标准；零 sorry。转向成功，无处方。

## 2026-07-23 H7 prolate Rayleigh-gap implementation CI 通过

- 冻结实现 commit `4404a93e92777c904563cda68120e9a1057e084e` 已通过公开 Lean Action
  run `29965379529`、build job `89075616914`（`2m36s`）。
- 公开 runner 独立重建了 247 行生产模块、一个 proven 与一个 open Target、十二条 exact
  TargetChecks 和十一项 standard-only 公理审计。Lean 证明源码现冻结。
- 下一步只提交不可变实现证据并要求该证据提交自身通过公开 CI；随后发布最终台账。真实
  arithmetic/prolate ratio、双极限、ground-state orientation、transform transfer、H7 与 RH 保持
  open；持续 RH Goal active。
- immutable-evidence commit `1e0c560293e189a4f02c5fc67f6de2758a239b28` 已通过公开 Lean
  Action run `29965651199`、build job `89076440184`（`1m45s`）。本 campaign 在注册的 generic
  Rayleigh-gap consumer 与 collapsing-gap falsification endpoint 停止；仅待 final-ledger commit
  及其 CI。source ratio、H7、RH、历史遗漏搜索、原创猜想和直接攻击保持 open。

## 2026-07-23 H7 公开闭合并选定 H1 theta=infinity 历史机制

- H7 final-ledger commit `5e36c53da657b4018f23339d4744562da07002ba` 已通过公开 Lean
  Action run `29965855724`、build job `89077075898`（`1m51s`）。generic Rayleigh-gap
  consumer/falsification campaign 完整闭合；真实 source ratio、H7 与 RH 保持 open。
- 对 D3/H1 的原始文献复核发现图谱需要修正：普通 critical-line proportion one 确实允许稀疏
  离线例外，但 Farmer 的完整 `theta=infinity` mollifier 猜想并不止推出比例一。Bettin--Gonek
  证明，固定 `theta` 的整段统一 moment 上界排除 `Re(s)>1/2+1/(2 theta)` 内的零点，而任意大
  `theta` 直接推出 RH。
- 下一 campaign 选定 `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01`。固定端点是精确
  mollifier/moment 定义、整数到实截断的凸插值、幂指数障碍消费者、固定 `theta` 的 quasi-RH
  边界及 all-`theta` RH 消费者。Mellin 卷积、移线留数和由 moment 假设产生幂障碍的解析桥保持
  open，不能作为已证前提。
- 该选择不是继续优化临界线百分比；它审计一条原图谱遗漏的、直接排除每个离线零点的历史
  机制。预注册公开 CI 前不编辑 Lean 证明源码；六个受保护文件保持未触碰、未暂存。
- 预注册 commit `1cb89557a3630778270da171ba59d87b1fa1f132` 已通过公开 Lean Action
  run `29966502725`、build job `89079059819`（`1m56s`）。固定 proof-source gate 已打开；
  公开绿灯前未创建任何新 Lean 证明源码。

## 2026-07-23 H1 theta=infinity consumer 本地实现完成

- 新模块 `LeanLab/Riemann/ThetaInfinityMollifier.lean` 精确定义 `M_x(s)`、`I_x(T1,T2)`、固定
  `theta` 的 uniform moment 前件、Farmer theta-infinity 猜想和 Bettin--Gonek power obstruction。
- 对 `N<=x<=N+1`，Lean 证明 `M_x` 在坐标 `1/log x` 中是 `M_N,M_(N+1)` 的凸组合；新端点
  系数因 `log 1=0` 消失。平方模凸性、critical-line 连续性和区间可积性把该结论提升到 source
  moment `I_x`。论文从整数 `N` 到实数 `y` 的量词切换因此通过，不构成 proof gap。
- 幂指数消费者证明：`T^(2 beta theta) << T^(1+epsilon+theta)` 对每个正 epsilon 成立时，
  `beta<=1/2+1/(2 theta)`；由此得到 fixed-theta zeta zero-free half-plane，并用 `rho -> 1-rho`
  反射证明 all-positive-theta obstruction 推出 Mathlib RH。
- `1/2+1/(4 theta)` 编译为 fixed-theta 边界内的严格离线 witness，防止把 quasi-RH 误称 RH。
  `FarmerThetaInfinityConjecture` 与 `BettinGonekMomentToPowerBridge` 都只是未决前件的精确定义，
  没有 proving theorem；Mellin/contour/residue bridge 与 arbitrary-length moment 仍 open。
- 两个 proven 与两个 open Targets、十二条 exact TargetChecks、十二项 selected axiom prints
  通过；选定定理公理仅 `propext`、`Classical.choice`、`Quot.sound`。定义对齐见
  `research/h1_theta_infinity_consumer_definition_alignment_20260723.md`；生产扫描为空，
  `git diff --check` 与全项目 `8,751`-job build 通过。public implementation CI 为下一道门。
- 冻结实现提交 `ed9fb11e3293e80a86561f30eb05073bfbf0b7ab` 已通过公开 Lean Action run
  `29967710426`、build job `89082709000`，耗时 `2m3s`。Lean 证明源码冻结；下一门是不可变证据
  提交及其独立公开 CI。
- 不可变证据提交 `877511c7ae47ba96b1334359d6e6a5c934694ac5` 已通过公开 Lean Action run
  `29967964091`、build job `89083481677`，耗时 `2m18s`。最终 ledger CI 是本 campaign 的最后
  发布门；闭合后两个开放解析边仍回到价值排序，H1/mollifier 家族不标记为耗尽。

## 2026-07-23 H1 Bettin--Gonek auxiliary campaign 预注册

- H1 theta-infinity consumer 最终 ledger `d4196d0f47d42f1c95d29b48dd341b9a469c514b` 已通过公开
  Lean Action run `29968166845`、build job `89084084918`，耗时 `1m54s`。consumer campaign
  公开闭合，但 analytic bridge、Farmer moment、H1 与 RH 均 open。
- 下一节点 `H1-BETTIN-GONEK-AUXILIARY-REGULARIZATION-01` 直接复原论文 equations
  `(2.2)`--`(2.3)`：以现有 entire `zetaPoleRemoved` 和 Mathlib `dslope` 同时正规化 zeta 极点与
  selected-zero 商，证明 source formula equality、`Re(w)>-1` 上全纯性、精确 selected-pole
  coefficient 及其非零性。
- campaign `LITERATURE-20260723-H1-BETTIN-GONEK-AUXILIARY-01` 已预注册；公开 prereg CI
  通过前不得创建生产 Lean 模块。Mellin inversion、decay、contour shift、convolution、完整
  moment-to-power bridge、Farmer 猜想与 RH 均不在本 endpoint。

## 2026-07-23 H1 Bettin--Gonek auxiliary 本地结果

- 预注册提交 `452e266613b7c8444de9366f1f65a6c1352dd219` 已通过公开 Lean Action run
  `29968683311`、build job `89085640497`，耗时 `2m13s`；证明源码在此后才创建。
- 277 行新模块 `LeanLab/Riemann/BettinGonekAuxiliary.lean` 用 `dslope zetaPoleRemoved rho`
  编译 source quotient 的真正全纯延拓，证明 raw `G_t` 对齐及 `Re(w)>-1` 上全纯性，并证明
  selected-pole 的精确 punctured limit 与非零性。没有发现本层 source normalization gap。
- 一个新 proven Target、十条 exact TargetChecks 与七项 selected axiom prints 通过；所选声明
  仅依赖 `propext`、`Classical.choice`、`Quot.sound`。生产禁用项扫描为空，direct compiles、
  `git diff --check` 与 8,752-job full build 均通过。冻结实现提交
  `2dd7fcb2284b9fe9afd3e01792a6a6c199a770f9` 已通过公开 Lean Action run `29969572291`、
  build job `89088421970`，耗时 `2m4s`；Lean 源码冻结。不可变证据提交
  `fdd688ba7e2157ec616b8f58a366b86c94c7f0e9` 也已通过 run `29969746284`、build job
  `89088970037`，耗时 `2m0s`；最终 ledger 尚待发布。
- 未证明且不可用的边仍是 Mellin/convolution、`G_t` decay、contour shift、residue lower
  bound、完整 moment-to-power bridge、Farmer moment 与 RH。

## 2026-07-23 H7 Weil pole block 选题

- H1 auxiliary 最终 ledger `b3c967d64a7c9df3cec8c251a302190e516aad81` 已通过公开 Lean
  Action run `29969901015`、build job `89089454873`，耗时 `2m0s`；该局部 campaign 公开闭合，
  H1 解析桥与 RH 仍 open。
- 跨路线重排选择 `H7-WEIL-POLE-RANK-TWO-INSTANTIATION-01`：实例化实际 source pole
  divided-difference matrix，核对其系数、闭式条目及 even-positive minus odd-positive 秩一分解。
- campaign `LITERATURE-20260723-H7-WEIL-POLE-BLOCK-01` 已预注册；公开 prereg CI 通过前不得
  创建生产 Lean 模块。prime/archimedean blocks、总 Weil matrix、Herglotz scalar bound、
  simple-even、ground/prolate limit 与 RH 均不在本 endpoint。

## 2026-07-23 H7 Weil pole block 本地结果

- 预注册提交 `c17a3be17b585f349972e0fb7f9d8541839f3dea` 已通过公开 Lean Action run
  `29970453996`、build job `89091164213`，耗时 `1m54s`；证明源码在此后才创建。
- 250 行 `LeanLab/Riemann/WeilGroundStatePoleBlock.lean` 从实际 `psi_0` value/derivative
  samples 构造 divided-difference matrix，证明 source closed entry、正系数、exact even-minus-odd
  rank-two decomposition、全向量二次型公式及 parity sign laws。没有发现 source normalization
  mismatch。
- 一个 proven actual-source Target、九条 exact TargetChecks、七项 standard-only axiom prints、
  空禁用项扫描、`git diff --check` 与 8,753-job full build 均通过。冻结实现提交
  `4b22712b531df010901e9813710b8ad145e60392` 已通过公开 Lean Action run `29971043533`、
  build job `89092937602`，耗时 `2m30s`；Lean 源码冻结。不可变证据提交
  `58665041b17686cf6ac02abd2b89a295406838f4` 通过 run `29971296016`、build job
  `89093681779`，耗时 `1m34s`；仅待最终 ledger CI。
- pole block 在 even sector 非负、odd sector 非正，因此 total simple-even 仍必须使用
  prime/archimedean blocks 的全局平衡。Herglotz scalar bound、source limits、H7 与 RH 仍 open。
