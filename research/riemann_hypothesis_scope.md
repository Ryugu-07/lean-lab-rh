# 黎曼猜想首轮研究范围

更新时间：2026-07-09

## 研究边界

本项目的近期目标不是宣称解决黎曼猜想，而是建立一条可复盘的证明工程流程：

1. 用 mathlib 中的 `RiemannHypothesis` 作为形式化目标。
2. 所有中间数学断言先落到 Lean4；凡是不能无占位证明编译通过的断言，都只能作为“想法/待证”，不能作为下一步证明的前提。
3. 每次尝试记录 statement、来源、策略、Lean 编译结果、失败原因和下一步。
4. 人类文献只给路线和启发；进入项目主线的定理必须回到 Lean。

## 2026-07-09 审查后修订

根据 `/Users/karasuakamatsu/Downloads/review_rh_loop_goal_20260709.md`，当前主线从
“持续生成可编译引理”改为“目标账本 + blueprint 驱动”：

- Tier 1：把本地 `riemannXi` / Li scaffold 收尾成可交付成果。优先目标是补齐
  `riemannXi` 与标准 completed zeta / 非平凡 zeta 零点之间的桥接，引导
  `liCoefficientCandidate 1` 的正性或精确 gap 报告，并写一页结果说明。
- Tier 2：在 Li 判据/Hadamard 路线与 Nyman-Beurling/Baez-Duarte 路线之间二选一；选择前
  必须先做 mathlib 库存盘点。
- Tier 3：`RiemannHypothesis` 只作为长期地平线，不作为直接 loop 目标。

新的执行文件：

- 目标账本：`LeanLab/Riemann/Targets.lean`。
- Loop 协议：`research/rh_loop_protocol_20260709.md`。
- Blueprint：`research/blueprint.md`。

执行纪律：

- 每个 loop 开跑前预注册 statement 或库存问题。
- 每个 loop 必须消掉一个目标账本项、填一个 blueprint 节点、完成一次有界库存，或记录一个明确失败路线。
- 纯改写 loop 不连续超过两次；数值估计尽量批处理。
- 每 10 个 loop 做一次元审查：如果目标账本和 blueprint 都没有推进，则停下重规划。

mathlib 当前定义的目标是：

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0)
    (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
    s.re = 1 / 2
```

也就是说，我们的形式化对象是：若 `ζ(s)=0`，且该零点不是负偶整数形式的平凡零点，同时 `s ≠ 1`，则 `Re(s)=1/2`。

## mathlib 已有材料

已在本地 mathlib v4.31.0 中确认：

- `riemannZeta` 已定义为 Hurwitz zeta 的延拓版本。
- `RiemannHypothesis` 已在 `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` 中定义。
- `riemannZeta_neg_two_mul_nat_add_one`：负偶整数处的平凡零点。
- `riemannZeta_one_sub`：zeta 函数方程相关版本。
- `zeta_eq_tsum_one_div_nat_cpow`：`1 < Re(s)` 时的 Dirichlet 级数表达。
- `riemannZeta_eulerProduct*`：`1 < Re(s)` 时的 Euler product。
- `riemannZeta_ne_zero_of_one_le_re`：`1 ≤ Re(s)` 时 zeta 不为零。
- `riemannZetaZeros`、`isClosed_riemannZetaZeros`、`isDiscrete_riemannZetaZeros`：零点集合、闭性和离散性。

首批项目内包装见 `LeanLab/Riemann/Basic.lean`，目前只包含可由 mathlib 直接推出的小结论。

2026-07-08 loop 01 新增：

- `RiemannHypothesis.nontrivial_zero_inCriticalStrip`：在 RH 假设下，项目定义的非平凡零点属于开临界带。
- 这是条件性包装定理，作用是给后续路线提供统一接口；它不是 RH 的无条件推进。

2026-07-08 loop 02 新增：

- `trivial_zero_re_lt_zero`：每个标准平凡零点位置 `-2 * (n + 1)` 的实部严格小于 0。
- 这是无条件小引理，用于把平凡零点与开临界带分离。

2026-07-08 loop 03 新增：

- `trivial_zero_not_inCriticalStrip`：每个标准平凡零点位置都不在开临界带内。
- 当前 trivial-zero 包装已够后续使用；下一步转向 completed zeta / xi / Li 判据支撑调查。

2026-07-08 loop 04 新增：

- 新文件 `LeanLab/Riemann/LiScaffold.lean`。
- 本地定义 `riemannXi s = s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2`。
- 已证明 `riemannXi_one_sub`：`riemannXi (1 - s) = riemannXi s`。
- 调查结论：当前 mathlib 版本有 `completedRiemannZeta₀` 和函数方程，但未发现可直接使用的 `riemannXi` 声明；Li 判据路线需要本地搭建 xi 和导数接口。

2026-07-08 loop 05 新增：

- 已证明 `differentiable_riemannXi`：本地 `riemannXi` 在 `ℂ` 上可微。
- 证明中需要显式使用 `differentiable_completedZeta₀`；`fun_prop` 不会自动发现这条 zeta₀ 可微性定理。
- Li 判据路线下一步可以先定义 derivative-based Li coefficient expression，但不能声称 RH 等价。

2026-07-08 loop 06 新增：

- 已定义 `liCoefficientCandidate n`：
  `iteratedDeriv (n + 1) (fun s => s ^ n * log (riemannXi s)) 1 / n!`。
- 已证明 `liCoefficientCandidate_zero`：`n = 0` 时它等于 `deriv (fun s => log (riemannXi s)) 1`。
- 这只是 Li 系数候选表达式；尚未证明 log 的局部解析性、xi 在 `1` 附近非零、正性条件或 RH 等价。

2026-07-08 loop 07 新增：

- 已证明 `riemannXi_one`：`riemannXi 1 = 1 / 2`。
- 已证明 `riemannXi_one_ne_zero`：`riemannXi 1 ≠ 0`。
- 这为后续讨论 `log ∘ riemannXi` 在 `1` 附近的可微/解析性提供点值基础，但还不是局部非零性或解析对数定理。

2026-07-08 loop 08 新增：

- 已证明 `riemannXi_one_mem_slitPlane`：`riemannXi 1 ∈ slitPlane`。
- 已证明 `analyticAt_riemannXi`：本地 `riemannXi` 在每一点解析。
- 已证明 `analyticAt_log_riemannXi_one`：`fun s => log (riemannXi s)` 在 `1` 处解析。
- 这是对主支 `Complex.log` 的点态安全使用；尚未证明全局对数解析性、Li 正性条件或 RH 等价。

2026-07-08 loop 09 新增：

- 已证明 `differentiableAt_log_riemannXi_one`。
- 已证明 `hasDerivAt_log_riemannXi_one`：`log ∘ riemannXi` 在 `1` 处的导数是 `deriv riemannXi 1 / riemannXi 1`。
- 已证明 `liCoefficientCandidate_zero_eq_logDeriv`：第一个候选系数等于该对数导数。
- 这仍是局部导数合法性，不是 Li 正性条件或 RH 等价。

2026-07-08 loop 10 新增：

- 已证明 `deriv_riemannXi_factor_one`：`deriv (fun s => s * (s - 1) / 2) 1 = 1 / 2`。
- 已证明 `deriv_riemannXi_one`：`deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2`。
- 已证明 `liCoefficientCandidate_zero_eq_completedZeta₀`：第一个 Li 候选系数等于 `completedRiemannZeta₀ 1`。
- 这是乘积求导和定义化简；并未证明 `completedRiemannZeta₀ 1` 的数值、正性或 RH 等价。

2026-07-08 loop 11 新增：

- 本地 mathlib 搜索发现 `Mathlib.NumberTheory.Harmonic.ZetaAsymp` 中已有
  `completedRiemannZeta₀_one`。
- 已证明 `liCoefficientCandidate_zero_eq_eulerMascheroni`：第一个 Li 候选系数等于
  `((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1`。
- 这是特殊值代入；尚未证明该表达式为实、为正，或任何 Li 判据/RH 等价。

2026-07-08 loop 12 新增：

- 已证明 `liCoefficientCandidate_zero_eq_ofReal`：第一个 Li 候选系数等于实数
  `((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ)` 在 `ℂ` 中的嵌入。
- 证明中使用 `Complex.ofReal_log` 和 `4 * Real.pi` 的正性。
- 这是实值化步骤；尚未证明该实数严格为正。

2026-07-08 loop 13 新增：

- 已证明 `liCoefficientCandidate_zero_real_pos`：
  `0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1`。
- 已证明 `liCoefficientCandidate_zero_re_pos`：第一个 Li 候选系数的实部严格为正。
- 证明使用 `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 11`、
  `Real.log_two_lt_d9`、`Real.log_three_lt_d9`、`Real.pi_lt_d4`、
  `Real.log_le_sub_one_of_pos` 和一个有理数比较。
- 这是 `n = 0` 的正性检查；尚未证明任意 `n` 的 Li 正性条件。

2026-07-08 loop 14 新增：

- 已证明 `liCoefficientCandidate_one_eq_secondDeriv`：第二个本地 Li 候选项等于
  `deriv (deriv (fun s => s * log (riemannXi s))) 1`。
- 已证明 `deriv_id_mul_log_riemannXi_one`：`fun s => s * log (riemannXi s)` 在 `1`
  处的一阶导数等于 `log (riemannXi 1) + deriv riemannXi 1 / riemannXi 1`。
- 已证明 `deriv_id_mul_log_riemannXi_one_eq_completedZeta₀`：该一阶导数等于
  `log (1 / 2 : ℂ) + completedRiemannZeta₀ 1`。
- 这是 `n = 1` 的导数脚手架；尚未计算二阶导数或证明第二项正性。

2026-07-08 loop 15 新增：

- 已证明 `analyticAt_id_mul_log_riemannXi_one`：`fun s => s * log (riemannXi s)` 在 `1` 处解析。
- 已证明 `analyticAt_deriv_id_mul_log_riemannXi_one` 和
  `differentiableAt_deriv_id_mul_log_riemannXi_one`：其导函数在 `1` 处解析并可微。
- 已证明 `hasDerivAt_deriv_id_mul_log_riemannXi_one`：该导函数在 `1` 处的导数值是
  `liCoefficientCandidate 1`。
- 这是第二个候选项的解析可微性接口；尚未给出显式二阶导数或正性。

2026-07-09 loop 22 新增：

- 已证明 `analyticAt_deriv_completedRiemannZeta₀_one` 和
  `differentiableAt_deriv_completedRiemannZeta₀_one`：`deriv completedRiemannZeta₀` 在 `1`
  处解析并可微。
- 已证明 `deriv_deriv_riemannXi_one`：
  `deriv (deriv riemannXi) 1 =
    completedRiemannZeta₀ 1 + deriv completedRiemannZeta₀ 1`。
- 已证明 `liCoefficientCandidate_one_eq_completedZeta₀_deriv`：
  `liCoefficientCandidate 1 =
    4 * completedRiemannZeta₀ 1 +
      2 * deriv completedRiemannZeta₀ 1 - completedRiemannZeta₀ 1 ^ 2`。
- 这把第二个候选项降到 `completedRiemannZeta₀` 在 `1` 处的值和一阶导；尚未计算该导数或证明第二个候选项正性。

2026-07-09 loop 23 新增：

- 已证明 `deriv_completedRiemannZeta₀_one_eq_neg_zero`：
  `deriv completedRiemannZeta₀ 1 = -deriv completedRiemannZeta₀ 0`。
- 已证明 `liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero`：
  `liCoefficientCandidate 1 =
    4 * completedRiemannZeta₀ 1 -
      2 * deriv completedRiemannZeta₀ 0 - completedRiemannZeta₀ 1 ^ 2`。
- 已证明 `liCoefficientCandidate_one_eq_eulerMascheroni_neg_deriv_zero`：把上一式中的
  `completedRiemannZeta₀ 1` 替换为欧拉常数和 `log (4π)` 的已知表达式。
- 本地搜索尚未发现 `deriv completedRiemannZeta₀ 1` 的直接特殊值；导数反号结论来自
  `completedRiemannZeta₀_one_sub` 的函数方程。

2026-07-09 loop 24 新增：

- 已证明 `deriv_riemannZeta_zero_numerator`：
  `deriv (fun s : ℂ ↦ (s * completedRiemannZeta₀ s - 1) - s / (1 - s)) 0 =
    completedRiemannZeta₀ 0 - 1`。
- 这说明 mathlib 中 `ζ'(0)` 计算的分子侧只依赖 `completedRiemannZeta₀ 0`，而不会暴露
  `deriv completedRiemannZeta₀ 0`；原因是 `s * completedRiemannZeta₀ s` 的导数在 `0`
  处把 `completedRiemannZeta₀` 的导数项乘成零。
- 分母导数的独立包装曾尝试但未收录；它需要更细地处理 `deriv` 下的函数乘法形状和
  Gamma 极点避让条件。

2026-07-09 loop 25 新增：

- 已证明 `completedRiemannZeta₀_zero_eq_one`：`completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1`。
- 已证明 `liCoefficientCandidate_zero_eq_completedZeta₀_zero`：
  `liCoefficientCandidate 0 = completedRiemannZeta₀ 0`。
- 已证明 `liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero`：
  `liCoefficientCandidate 1 =
    liCoefficientCandidate 0 * (4 - liCoefficientCandidate 0) -
      2 * deriv completedRiemannZeta₀ 0`。
- 这是第二个本地 Li 候选项目前最紧凑的表达式；剩余未知集中在
  `deriv completedRiemannZeta₀ 0`。

2026-07-09 loop 26 新增：

- 已证明 `liCoefficientCandidate_zero_im_eq_zero`：第一个本地 Li 候选项虚部为零。
- 已证明 `liCoefficientCandidate_one_im_eq_neg_two_deriv_completedZeta₀_zero_im`：
  `(liCoefficientCandidate 1).im = -2 * (deriv completedRiemannZeta₀ 0).im`。
- 已证明 `liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re`：
  `(liCoefficientCandidate 1).re =
    (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
      2 * (deriv completedRiemannZeta₀ 0).re`。
- 这把第二个本地 Li 候选项的实值性和实部正性瓶颈明确集中到
  `deriv completedRiemannZeta₀ 0` 的实部/虚部。

2026-07-09 loop 27 新增：

- 已导入 `Mathlib.Analysis.Calculus.Deriv.Star`，使用 mathlib 的共轭导数定理
  `deriv_conj_conj`。
- 已证明 `deriv_zero_im_eq_zero_of_conj_conj_eq_self`：若 `f : ℂ → ℂ` 满足
  `((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) = f`，则 `(deriv f 0).im = 0`。
- 已证明 `deriv_completedRiemannZeta₀_zero_im_eq_zero_of_conj_conj`：把上一桥接定理专门化到
  `completedRiemannZeta₀`。
- 已证明 `liCoefficientCandidate_one_im_eq_zero_of_completedZeta₀_conj_conj`：一旦能证明
  `completedRiemannZeta₀` 的函数级共轭兼容性，就可推出第二个本地 Li 候选项虚部为零。
- 这不是 `completedRiemannZeta₀` 共轭兼容性的证明；它把后续真正需要证明的缺口精确固定为一个函数级对称性命题。

2026-07-09 loop 28 新增：

- 已证明 `mellin_conj_of_forall_mem_Ioi`：若 `f : ℝ → ℂ` 在正实轴上被复共轭固定，则
  `mellin f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mellin f s)`。
- 已证明 `hurwitzEvenFEPair_zero_f_modif_conj`：`(hurwitzEvenFEPair 0).f_modif` 被复共轭固定。
- 已证明 `hurwitzEvenFEPair_zero_Λ₀_conj`：零参数 even Hurwitz FE-pair 的 `Λ₀` 满足共轭兼容性。
- 已证明 `completedRiemannZeta₀_conj` 和 `completedRiemannZeta₀_conj_conj`：
  `completedRiemannZeta₀` 满足函数级共轭兼容性。
- 已证明 `deriv_completedRiemannZeta₀_zero_im_eq_zero`：
  `(deriv completedRiemannZeta₀ 0).im = 0`。
- 已证明 `liCoefficientCandidate_one_im_eq_zero`：
  `(liCoefficientCandidate 1).im = 0`。
- 这把第二个本地 Li 候选项的实值性问题闭合；剩余瓶颈转为
  `(deriv completedRiemannZeta₀ 0).re` 的结构公式或足够的不等式。

2026-07-09 loop 29 新增：

- 已证明 `deriv_completedRiemannZeta₀_zero_eq_ofReal_re`：`deriv completedRiemannZeta₀ 0`
  等于其实部作为复数的嵌入。
- 已证明 `liCoefficientCandidate_one_eq_ofReal_re`：第二个本地 Li 候选项等于其实部作为复数的嵌入。
- 已证明 `liCoefficientCandidate_one_eq_ofReal_re_formula`：
  `liCoefficientCandidate 1 =
    (((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
      2 * (deriv completedRiemannZeta₀ 0).re : ℝ) : ℂ)`。
- 已证明 `liCoefficientCandidate_one_re_pos_iff_re_formula`：第二个本地 Li 候选项的实部正性等价于上述显式实数表达式的正性。
- 这把下一步目标固定为一个纯实数不等式；仍未证明该不等式。

2026-07-09 loop 30 新增：

- 已证明通用引理 `deriv_eq_zero_at_half_of_one_sub_eq_self`：若复函数满足
  `f (1 - s) = f s`，则 `deriv f (1 / 2) = 0`。
- 已证明 `deriv_riemannXi_half_eq_zero`：
  `deriv riemannXi (1 / 2) = 0`。
- 已证明 `deriv_completedRiemannZeta₀_half_eq_zero`：
  `deriv completedRiemannZeta₀ (1 / 2) = 0`。
- 这是函数方程中心对称性的局部导数后果，可作为后续围绕 `1 / 2` 的 Taylor/局部偶性
  尝试的可靠入口；它仍不提供 `(deriv completedRiemannZeta₀ 0).re` 的数值或不等式。

2026-07-09 loop 31 新增：

- 已证明 `half_sub_eq_of_one_sub_eq_self` 和 `centered_even_of_one_sub_eq_self`：若
  `f (1 - s) = f s`，则 `f (1 / 2 - z) = f (1 / 2 + z)`，等价地中心化函数
  `z ↦ f (1 / 2 + z)` 为偶函数。
- 已专门化到 `riemannXi` 与 `completedRiemannZeta₀`：
  `riemannXi_half_sub`、`centered_riemannXi_even`、
  `completedRiemannZeta₀_half_sub`、`centered_completedRiemannZeta₀_even`。
- 已证明 `deriv_centered_zero_of_one_sub_eq_self` 及其两个专门化：
  中心化后的 `riemannXi` 与 `completedRiemannZeta₀` 在 `0` 处一阶导数为零。
- 这是从函数方程进入 Taylor 系数语言的下一层脚手架；仍未给出任意高阶奇系数消失定理。

2026-07-09 loop 32 新增：

- 已证明 `iteratedDeriv_odd_eq_zero_of_even`：若 `g (-z) = g z`，则
  `iteratedDeriv (2 * k + 1) g 0 = 0`。
- 已证明 `iteratedDeriv_centered_odd_eq_zero_of_one_sub_eq_self`：若
  `f (1 - s) = f s`，则中心化函数 `z ↦ f (1 / 2 + z)` 的所有奇数阶
  `iteratedDeriv` 在 `0` 处为零。
- 已专门化到本地 `riemannXi` 和 `completedRiemannZeta₀`：
  `iteratedDeriv_centered_riemannXi_odd_eq_zero`、
  `iteratedDeriv_centered_completedRiemannZeta₀_odd_eq_zero`。
- 这把函数方程的中心偶性正式转化成 Taylor/导数序列层面的结构约束；偶数阶导数和
  正性问题仍未解决。

2026-07-09 loop 33 新增：

- 已证明 `iteratedDeriv_centered_eq`：中心化函数 `z ↦ f (1 / 2 + z)` 在 `0` 处的任意阶
  `iteratedDeriv` 等于原函数在 `1 / 2` 处的对应阶 `iteratedDeriv`。
- 已专门化到 `riemannXi` 与 `completedRiemannZeta₀`，并证明二阶版本分别等于
  `deriv (deriv riemannXi) (1 / 2)` 与
  `deriv (deriv completedRiemannZeta₀) (1 / 2)`。
- 已证明 `deriv_deriv_riemannXi_half`：
  `deriv (deriv riemannXi) (1 / 2) =
    completedRiemannZeta₀ (1 / 2) -
      (1 / 8) * deriv (deriv completedRiemannZeta₀) (1 / 2)`。
- 已证明 `iteratedDeriv_centered_riemannXi_two_eq_completedZeta₀_half`，把中心化 `riemannXi`
  的二阶 `iteratedDeriv` 写成同一表达式。
- 这是偶数阶中心 Taylor 数据的第一条具体公式；它仍未给出 `1 / 2` 点特殊值或符号信息。

2026-07-09 loop 34 新增：

- 已证明通用桥 `value_im_eq_zero_of_conj_conj_eq_self_at_fixed`：满足共轭兼容性的复函数在
  共轭固定点取实值。
- 已证明 `deriv_conj_conj_eq_self`：共轭兼容性可传递到导函数。
- 已证明 `completedRiemannZeta₀` 的导函数与二阶导函数共轭兼容：
  `deriv_completedRiemannZeta₀_conj_conj`、
  `deriv_deriv_completedRiemannZeta₀_conj_conj`。
- 已证明中心值和中心二阶导数实值：
  `completedRiemannZeta₀_half_im_eq_zero`、
  `deriv_deriv_completedRiemannZeta₀_half_im_eq_zero`，以及对应的实数嵌入版本。
- 已证明中心化 `riemannXi` 的二阶 `iteratedDeriv` 也是实值：
  `iteratedDeriv_centered_riemannXi_two_im_eq_zero`、
  `iteratedDeriv_centered_riemannXi_two_eq_ofReal_re`。
- 这为后续中心侧实数不等式尝试提供接口；尚未证明任何符号或正性。

2026-07-09 loop 35 新增：

- 本地搜索未发现 `completedRiemannZeta₀ (1 / 2)` 或
  `deriv (deriv completedRiemannZeta₀) (1 / 2)` 的直接 special value/符号定理。
- 已证明 `iteratedDeriv_centered_riemannXi_two_re_eq_completedZeta₀_half_re`：
  中心化 `riemannXi` 二阶导数的实部等于
  `(completedRiemannZeta₀ (1 / 2)).re -
    (1 / 8) * (deriv (deriv completedRiemannZeta₀) (1 / 2)).re`。
- 已证明 `iteratedDeriv_centered_riemannXi_two_eq_ofReal_re_formula`：
  中心化二阶导数本身等于上述实数表达式在 `ℂ` 中的嵌入。
- 已证明 `iteratedDeriv_centered_riemannXi_two_re_pos_iff`：其正实部目标等价于这个纯实数
  不等式。
- 这把中心侧符号目标整理成实数不等式；尚未证明该不等式。

2026-07-09 loop 36 新增：

- 已证明 `riemannXi_half`：
  `riemannXi (1 / 2) = 1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2)`。
- 已证明中心化零阶项：
  `iteratedDeriv_centered_riemannXi_zero_eq_half`、
  `iteratedDeriv_centered_riemannXi_zero_eq_completedZeta₀_half`。
- 已证明 `riemannXi (1 / 2)` 为实值：
  `riemannXi_half_im_eq_zero`、`riemannXi_half_eq_ofReal_re`。
- 已证明 `riemannXi_half_re_eq_completedZeta₀_half_re`、
  `riemannXi_half_eq_ofReal_re_formula`、`riemannXi_half_re_pos_iff`，把中心值正实部目标化为
  `0 < 1 / 2 - (1 / 8) * (completedRiemannZeta₀ (1 / 2)).re`。
- 这补齐了中心 Taylor 的零阶数据；仍未证明中心值正性。

2026-07-09 loop 37 新增：

- 已证明 `completedRiemannZeta₀_half_eq_riemannXi_half`：
  `completedRiemannZeta₀ (1 / 2) = 4 - 8 * riemannXi (1 / 2)`。
- 已证明 `completedRiemannZeta₀_half_re_eq_riemannXi_half_re`：
  `(completedRiemannZeta₀ (1 / 2)).re = 4 - 8 * (riemannXi (1 / 2)).re`。
- 已证明 `riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four`：中心 `xi` 值正实部目标
  等价于 `(completedRiemannZeta₀ (1 / 2)).re < 4`。
- 已证明同一等价的中心化零阶 `iteratedDeriv` 版本。
- 这把中心值正性改写成 completed-zeta 中心值的上界问题；尚未证明该上界。

## 人类路线地图

### 1. Riemann 原始路线：显式公式、函数方程、临界线

Riemann 1859 论文从 Euler product 和 Dirichlet series 出发，引入解析延拓、函数方程、零点与素数计数之间的显式公式，并提出“所有相关根都应为实”的说法。按现代变量转换，这对应非平凡零点位于 `Re(s)=1/2`。

来源：
- Bernhard Riemann, “On the Number of Prime Numbers less than a Given Quantity”, Wilkins translation: <https://www.claymath.org/wp-content/uploads/2023/04/Wilkins-translation.pdf>

Lean 入口：
- Dirichlet series 与 Euler product 的右半平面版本。
- 函数方程与平凡零点。
- 后续若形式化显式公式，需要大量 Fourier/Mellin/分布理论基础。

### 2. Hadamard / de la Vallée Poussin：零点区域与素数定理

1896 年 Hadamard 和 de la Vallée Poussin 分别证明 `ζ(1+it) ≠ 0`，从而推出素数定理。mathlib 已有更适合我们直接使用的强包装：`1 ≤ Re(s)` 时 `riemannZeta s ≠ 0`。

来源：
- J. Hadamard, “Sur la distribution des zéros de la fonction ζ(s) et ses conséquences arithmétiques”, Bulletin de la Société Mathématique de France 24 (1896), 199-220: <https://www.numdam.org/item/BSMF_1896__24__199_1/>
- C. de la Vallée Poussin, “Recherches analytiques sur la théorie des nombres premiers”, Ann. Soc. Sci. Bruxelles 20 (1896), 183-256；条目见 NIST DLMF bibliography: <https://dlmf.nist.gov/bib/D>

Lean 入口：
- 已完成小结论：任何 zeta 零点满足 `Re(s) < 1`。
- 下一步可定义 closed/open half-plane、critical strip，并包装更多零点区域定理。

### 3. Weil 显式公式与正性判据

Weil 将显式公式推广成更结构化的形式；围绕 Weil positivity 的 RH 等价判据，是许多现代谱/非交换几何路线的共同骨架。

来源：
- A. Weil, “Sur les formules explicites de la théorie des nombres premiers”, Comm. Sém. Math. Univ. Lund (1952), 252-265；后续引用条目见 Numdam：<https://www.numdam.org/item/STNG_1981-1982__10__A3_0/>

Lean 入口：
- 需要先形式化测试函数空间、Fourier/Mellin 变换、显式公式的目标形态。
- 这个路线深，但可拆分成很多可验证引理。

### 4. Li 判据：正系数序列等价于 RH

Li 证明一列实数的非负性等价于 Dedekind zeta 的 RH；zeta 情况给出著名 Li coefficients。Bombieri-Lagarias 后续把这一类判据推广，并联系到 Guinand-Weil 显式公式。

来源：
- Xian-Jin Li, “The Positivity of a Sequence of Numbers and the Riemann Hypothesis”, Journal of Number Theory 65 (1997), 325-333: <https://www.sciencedirect.com/science/article/pii/S0022314X97921375>
- E. Bombieri and J. C. Lagarias, “Complements to Li's Criterion for the Riemann Hypothesis”, Journal of Number Theory 77 (1999), 274-287: <https://www.sciencedirect.com/science/article/pii/S0022314X99923922>

Lean 入口：
- 可能是首选路线之一：先形式化 `ξ` 函数、对数导数、有限阶导数表达。
- 风险在于 mathlib 是否已有足够的复可微高阶导数、Gamma/xi 包装。

### 5. Nyman-Beurling / Báez-Duarte：Hilbert 空间逼近等价

Nyman-Beurling 将 RH 转化为 `L²(0,∞)` 中某类分数部函数张成空间的闭包问题；Báez-Duarte 给出更强的离散/算术版本。

来源：
- Luis Báez-Duarte, “A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis”: <https://arxiv.org/abs/math/0202141>
- Luis Báez-Duarte, “A new necessary and sufficient condition for the Riemann hypothesis”: <https://arxiv.org/abs/math/0307215>
- Bhaskar Bagchi, survey on the Hilbert-space reformulation: <https://arxiv.org/abs/math/0607733>

Lean 入口：
- 可从 `L²`、闭包、简单函数逼近、分数部函数等对象拆起。
- 优点是逼近论/泛函分析命题更像 Lean 可分解任务；缺点是基础库覆盖度要先调查。

### 6. Hilbert-Pólya、Connes、Berry-Keating：谱解释

谱路线试图把非平凡零点的虚部解释为某个自伴算子的谱，从而由自伴性推出临界线。Connes 给出非交换几何和 Adele class space 的 trace formula 图景；Berry-Keating 提出与 `H = xp` 相关的半经典模型。

来源：
- Alain Connes, “Trace formula in noncommutative geometry and the zeros of the Riemann zeta function”: <https://arxiv.org/abs/math/9811068>
- M. V. Berry and J. P. Keating, “The Riemann Zeros and Eigenvalue Asymptotics”, SIAM Review 41 (1999), 236-266: <https://epubs.siam.org/doi/10.1137/S0036144598347497>
- Berry-Keating `H=xp` chapter: <https://link.springer.com/chapter/10.1007/978-1-4615-4875-1_19>

Lean 入口：
- 暂时只作为启发，不作为首轮主线。
- 若进入形式化，第一步也不是 RH，而是自伴算子谱定理、trace formula 组件和具体模型边界条件。

### 7. Montgomery-Odlyzko、随机矩阵与数值证据

Montgomery pair correlation 与 Odlyzko 的数值零点间距研究强烈支持 GUE 随机矩阵图景。这类证据指导结构猜想，但本身不是证明。

来源：
- H. L. Montgomery, “The pair correlation of zeros of the zeta function”, Proc. Symp. Pure Math. 24 (1973), 181-193；作者页扫描：<https://websites.umich.edu/~hlm/paircor1.pdf>
- A. M. Odlyzko, “On the distribution of spacings between zeros of the zeta function”, Mathematics of Computation 48 (1987), 273-308: <https://experts.umn.edu/en/publications/on-the-distribution-of-spacings-between-zeros-of-the-zeta-functio/>

Lean 入口：
- 不作为证明主线。
- 可作为后续计算实验和可视化方向，但不能替代 Lean 定理。

## 首轮拆分

1. Ground truth：在 Lean 中包装 `RiemannHypothesis`、非平凡零点、临界线、临界带。
2. 无条件零点区域：从 `riemannZeta_ne_zero_of_one_le_re` 推出任意 zeta 零点满足 `Re(s) < 1`。
3. RH 包装：证明 mathlib 的 `RiemannHypothesis` 等价于“所有项目定义的非平凡零点在临界线上”。
4. RH 条件接口：已证明在 RH 假设下，项目定义的非平凡零点落在开临界带内。
5. 平凡零点接口：已证明标准平凡零点位置的实部严格小于 0，并且不在开临界带内。
6. Li 判据脚手架：已定义本地 `riemannXi`，证明函数方程、全局可微性、`riemannXi 1 = 1 / 2`、`riemannXi 1 ≠ 0`、`riemannXi 1 ∈ slitPlane`、`log ∘ riemannXi` 在 `1` 处解析，定义 `liCoefficientCandidate`，证明第一个候选系数等于实数 `((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ)` 在 `ℂ` 中的嵌入且其实部严格为正，并建立第二个候选项的解析可微性接口、局部乘积法则展开接口、`log ξ` 导数到 `ξ'/ξ` 的局部改写接口、`ξ'` 的全局展开公式、`λ₁ = λ₀ + (λ₀ + L'(1))` 的局部对数导数层公式、`L'(1)` 的商法则展开、`λ₁` 到 `completedRiemannZeta₀ 1` 与 `deriv completedRiemannZeta₀ 1` 的局部化简、用函数方程把剩余导数改写到 `0` 点、证明 `ζ'(0)` 公式的分子侧不会给出该剩余导数、将 `λ₁` 压缩为 `λ₀ * (4 - λ₀) - 2 * deriv completedRiemannZeta₀ 0`、拆出 `λ₁` 的实部和虚部瓶颈公式、证明函数级共轭兼容性推出剩余导数实值的条件桥接定理、从 Mellin 变换和 real-valued Hurwitz kernel 结构证明 `completedRiemannZeta₀` 的函数级共轭兼容性，从而推出 `λ₁` 虚部为零，并把 `λ₁` 的正实部目标改写成一个纯实数不等式。
7. 文献筛选：把 Li 判据和 Nyman-Beurling/Báez-Duarte 作为首选可形式化路线；谱路线暂存为高层启发。
8. 下一批 Lean 任务：
   - 定义 `InCriticalStrip` 后，调查 mathlib 是否已有 `0 < Re(s)` 的无条件结论或函数方程可推出的左侧零点排除。
   - 若继续计算 `deriv completedRiemannZeta₀ 0` 的实部，需要二阶/Laurent 信息；一阶 `ζ'(0)` 的分子侧不足。
   - Loop 29 已把 `λ₁` 的正实部目标改写为纯实数不等式；下一步可尝试 `deriv completedRiemannZeta₀ 0` 的实部公式或足够的不等式。
   - 调查 `MeasureTheory` 中 `L²`、闭包和分数部函数是否足够支撑 Nyman-Beurling。

## 推进规则

- 文档可以记录猜想和路线；Lean 文件只收录已证明命题。
- 每次新增 Lean theorem 后必须运行：
  - `lake env lean <file>`
  - `lake build`
  - 对 `LeanLab attempts research` 运行占位证明关键字扫描
- 发现不能证明的命题：保留在 attempts 日志，标记为 blocked/pending，不得作为后续 theorem 的假设。
