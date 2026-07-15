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
- 预期管理：千禧年/希尔伯特难题是远期观察对象不是可交付物；近期可交付 = 本科级定理的 AI 辅助形式化。

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

## RH current handoff (2026-07-16, R5 Gaussian height-limit locally complete)

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
- Next: publish the immutable evidence backfill, verify its public CI, then return to fresh
  `INDEPENDENT_AUDIT -> ROUTE_SELECTION` without reopening this fixed endpoint.
- Implementation commit `00410cc2a6919acfa5835b121c47489c5105e0de` passed public Lean Action CI
  run `29436179027`, build job `87423295204`, in `2m23s`. Publish the immutable evidence backfill
  and require its own successful CI before final closure.

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
- No target-closure membership or residual convergence is proved. M2/G3 remains parked and the RH
  assumption frontier is unchanged. Do not spend the next campaign optimizing this constant or
  adding generic Gram wrappers. Enter `ROUTE_SELECTION` and require a precise target-coupling
  mechanism or select another route family.

## Previous RH handoff (2026-07-15, Discovery Protocol V3 route selection)

- The persistent RH goal is active. Commit `5d75abc` remains valid, but its `STOP` applies only to
  the exhausted automatic 2025-2026 recent-literature screening campaign. Local campaign stops now
  enter `ROUTE_SELECTION`; they do not stop the global goal.
- Wong arXiv `2310.03972v5` and Carvill arXiv `2510.18132` remain rejected. Preserve their Lean
  counterexamples and do not reopen those proof branches.
- `research/discovery_protocol_v3_20260715.md` records the global persistence, six-loop campaign,
  conjecture admission, anti-cycling, and progress-accounting rules.
- `research/route_portfolio.md` compares five route families. The selected campaign is
  `CAMPAIGN-20260715-GRAM-01`, exact Baez-Duarte Gram/projection geometry.
- `research/m2_gram_route_prereg_20260715.md` registers five candidate mechanisms, adversarial
  checks, nearest literature, and exactly one selected proof candidate: an explicit sparse lower
  frame bound for normalized kernels at indices `(2^24)^j`.
- All current eigenvalue and quadrature observations are `NUMERICAL_ONLY`. No new mathematical
  premise has been admitted, no Lean theorem has yet been added in this campaign, and M2/G3 remains
  parked with `hard_gap_delta=0`.
- Next work is one indivisible Lean proof attempt for the registered sparse bound. C1/C3 inputs
  must stay in that batch; partial helpers are not separate research loops.

## Previous RH handoff (2026-07-15, M2/G3 automatic literature campaign stopped)

- M0, M1, G1, G2, D, and G4/B1 remain complete; M2/G3 remains parked. No unconditional proof of
  RH or target closure membership is claimed.
- Audit `AUDIT-20260715-M2-G3-03` screened the remaining current 2025-2026 candidates. Iyer leaves
  the residual-covariance/Hilbert approximation bridge open; the Colombeau paper proves another
  RH equivalence; Bhattacharjee et al. use a mismatched `{x/k}` carrier and disclaim an RH proof;
  the dyadic project is conditional and numerical.
- No candidate supplied an unconditional estimate on the exact M0/M1-aligned carrier, so no Lean
  target or mathematical source edit was admitted. Classification: `NO_PROGRESS`, with
  `hard_gap_delta=0` and the assumption frontier unchanged. `git diff --check` and the unchanged
  8617-job project build pass.
- Audits M2-G3-01, M2-G3-02, and M2-G3-03 are three consecutive zero-delta loops. Loop Protocol
  v2 therefore requires `STOP`: do not resume automatic M2/G3 candidate generation without a new
  external source or independently proposed estimate that passes novelty and fixed-frontier
  admission.
- This is a protocol stop, not a proof that future research is impossible and not a `blocked`
  status for the persistent broad goal.
- Governance commit `6bdbd1f9a459edb1b0baa7d3568b44605f0d4fc6` passed public Lean Action CI
  run `29384810340`, build job `87255750317`, in 1m24s.

## Previous RH handoff (2026-07-15, Carvill branch falsified)

- M0, M1, G1, G2, D, and G4/B1 remain complete; M2/G3 remains parked. No unconditional proof of
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

- M0, M1, G1, G2, D, and G4/B1 remain complete; M2/G3 remains parked. No unconditional proof of
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

- M0, M1, G1, G2, and D remain complete; M2/G3 remains parked. No unconditional proof of RH or
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
  progress. F0-F5 must not be reopened for standalone helper lemmas, and M2/G3 remain parked.

## 黎曼猜想研究启动
- 2026-07-08：已按“证明工程/研究流程”启动 RH 首轮，不承诺解决 RH。
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

## Arch 审计：M1-18 / G1 关闭（2026-07-13，Claude）
- **审计结论：属实。** `riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure`（BaezDuarteForwardLimit.lean:1645）= Báez-Duarte 2002 正整数强化判据 ⟺ mathlib `RiemannHypothesis` 的完整等价。定义逐项对齐文献（χ_(0,1] / ρ(1/(nx)) n∈ℕ+ / L²(0,∞) / span 拓扑闭包）；公理审计独立复跑 31 条全部仅依赖三条标准公理；无 sorry/自定义公理/native_decide；iff 无额外假设。
- 定级：数学=已知定理；形式化=极可能任何证明助手首次（待 novelty audit），发表级。配套基建（1/ζ subpower、截断 Perron、ζ 凸性、Fourier–Mellin 等距）= mathlib 空缺。
- **发布前置条件与下一步方向：`~/Downloads/review_rh_m1_audit_20260713.md`**——Sol max 逐定理 review + Zulip 外审 + novelty audit 三关齐才可对外称"首次形式化"；新节点建议 mathlib 上游化为主线 + Burnol 下界 d_N²≳C/log N 为研究线；**G3（无条件构造）继续禁止作为 loop 目标**。协议微调三条：TargetChecks 补 iff witness、hard_gap_dag 收口 M1/D、新增对外发布 gate。

## Post-M1 治理与 P1 审查（2026-07-13）
- `AUDIT-20260713-POST-M1-01` 已给最终 iff 增加精确 `TargetChecks.lean` 类型见证，并把 G3 自动禁入、G4 Burnol 已知下界线和 P1-P3 发布门写入固定协议/DAG。
- P1 已由干净上下文 Sol 5.6 max 只读逐定理审查关闭：reverse、forward-limit、truncated-Perron 未发现 P0-P3 问题，决定 `CONTINUE`；记录见 `research/m1_sol_max_review_20260713.md`。P2 Zulip 外审与 P3 novelty audit 仍未完成，不得对外称“首次形式化”。
- 全项目 `lake build` 8608 jobs 通过；无 `sorry`/`admit`/`sorryAx`、无项目 `axiom`/`constant`。治理提交 `fba10e7` 通过公开 CI run `29224952001`、build job `86737084562`。本批分类 `FORMALIZATION_ONLY`，不改变 RH、M2 或 G3。

## G4-01 Burnol 下界依赖审计（2026-07-13）
- 原文主对象是连续参数复空间 `B_lambda = span{rho(theta/t) : lambda<=theta<=1}`，不是项目现有的全体正整数核闭包。对有限自然空间 `V_N`，正确包含为 `V_N <= B_(1/N)`，故距离方向为 `D(1/N) <= d_N`；因此 Burnol 下界可以向自然距离转移。
- 源证明固定拆为 F0 连续/自然陈述对齐、F1 unitary distance model、F2 Burnol 正交向量、F3 Gram/Cauchy 渐近、F4 有限零点集 liminf 下界、F5 全零点和与自然转移。详细矩阵见 `research/g4_burnol_dependency_audit_20260713.md`。
- 本轮分类 `DEPENDENCY_GAP_IDENTIFIED`，未新增 Lean 定理，不改变 M2/G3。下一批只能把 F0 的 span/distance/inclusion 一次性完成并记为 `FORMALIZATION_ONLY`；随后必须进入 F1 源级分析，禁止逐个包装距离引理刷轮次。

## G4-F0 连续/自然空间对齐（2026-07-13）
- `BurnolLowerBound.lean` 定义 Burnol 的连续参数核空间 `B_lambda`、有限自然核空间 `V_N` 及两个距离；Lean 验证 `V_N <= B_(1/N)` 与 `D(1/N) <= d_N`。
- Lean 同时验证 `1/N -> 0+`，因而后续 Burnol 的 `lambda -> 0+` liminf 结论可沿正确方向转移到自然子空间。这一批严格分类为 `FORMALIZATION_ONLY`，不改变 M2/G3。
- G4 下一个唯一允许的自动目标是 F1：源级审计并形式化 Burnol 的 unitary distance model `D(lambda)=dist(chi1,C_lambda)`。G3 仍停放。
- 实现提交 `1383db8e9cea271874b7f4f399eb35d1cf07f103`；公开 GitHub Actions run `29225515844`、build job `86738660740` 成功。

## G4-F1-01 unitary distance model 审计（2026-07-13）
- 原文距离等距的精确算子是 `T=(1-M)^-1`，临界线 Mellin 乘子为 `(s-1)/s`。符号核对为 `T chi=chi1`、`T rho(1/t)=-A`；负号不改变复 span。
- 归一化伸缩为 `D_theta f(t)=theta^(-1/2)f(t/theta)`，因此项目核 `rho(theta/t)=sqrt(theta)D_theta f(t)`；这一标量不改变 span，但必须在 Lean 映射定理中显式出现。
- 审计拒绝了把 `C_lambda` 直接定义成等距像的同义反复。F1 固定拆为 F1a（显式 Burnol `A` 的支撑、`L2`、Mellin 命题）与 F1b（乘子等距、核/span/距离转移）；下一批只选 F1a，G3 仍停放。
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
  的 `Y(lambda,s,k)` 存在性与正交性。M2/G3 保持停放。
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
  配对及解析阶正交性必须一起通过；F3 仍禁止提前开始，M2/G3 保持停放。
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
  继续停放。本地 8612-job 全构建、精确 TargetChecks、占位/声明扫描、axiom audit 与
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
- **改进方案（执行前必读）**：`~/Downloads/review_rh_loop_goal_20260709.md` — 目标三层化（Tier1=补 ξ/ζ 桥接引理+完成 λ₂+成文可 PR；Tier2=盘点后在 Li 判据 Hadamard 路线与 Nyman-Beurling 二选一；Tier3=RH 只当地平线）+ Targets.lean 目标账本 + blueprint DAG + loop 纪律五条（预注册/改写上限/先搜后证/每10 loop元审查/记否决路线）。
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
