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

## 双审计合议（2026-07-10，Claude arch × GPT-5.6 Sol）
- Sol 独立审计结论与 arch 7/09 审查一致：**合格的 RH 周边形式化工程，非 RH 逼近**；130 轮无伪证明/无公理走私，但 loop 膨胀严重（loop 131 只剩一行组合推论）。
- Claude 核查确认 Sol 三条硬主张：仓库仅 1 commit ✓；Targets.lean 是手填数据账本 ✓（且 `some `foo` 单反引号 Name 字面量不做存在性解析——双反引号才检查）；loop 协议规则可被"自造小目标"游戏化 ✓。
- **v2 协议已发布：`~/Downloads/rh_loop_protocol_v2_20260710.md`，取代 v1 与 repo 内 rh_loop_protocol_20260709.md 的规则部分。核心：暂停 loop 131、双轨道标签（FORMALIZATION/DISCOVERY）、hard_gaps.md 登记表、Targets 三层加固（双反引号+example witness+trusted-primitive audit）、每 loop 一 commit、审计者/实现者分离（5.5 实现、Sol max 每 5 loop 清洁上下文复审、Claude 裁判）。**
- 已执行治理检查点：导出 loop/goal 运行时配置给审计；新增 `research/hard_gap_dag.md`、`research/hard_gaps.md`、`research/loop_classification_20260710.md`；重写 `research/rh_loop_protocol_20260709.md` 的规则部分；新增 `LeanLab/Riemann/TargetChecks.lean` 并接入 build；`T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` 标记为机械 batch item。

## M0 清洁上下文审计（2026-07-10）
- `AUDIT-20260710-M0-01` 已由 Lean 证明 `nymanBeurlingConcreteApprox_unconditional`：unrestricted 谓词允许参数 `1` 和 `-1`，两者的 fractional-part kernel 在一个可数例外集之外相加为常数一，所以该谓词无需 RH 即成立。
- 结果分类为 `BRANCH_FALSIFIED`，不是 RH progress；详细对齐矩阵见 `research/m0_statement_alignment_20260710.md`。
- `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` 已停放为过时目标；不得把 unrestricted 谓词用于 M1 判据。
- 审计决策为 `PIVOT`：下一批只做 restricted closure 与 restricted concrete tolerance 的双向等价，并处理文献 `0 < theta < 1` 与项目 `0 < theta <= 1` 的端点差异。

## Arch 审查（2026-07-09，Claude）
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
