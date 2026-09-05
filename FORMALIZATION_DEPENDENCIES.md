# 无 epsilon 证明的 Lean 依赖盘点

> **后续更新：** 本文以下保留的是早期源码搜索与依赖快照，不再表示最新待办或构建状态。当前状态请读同目录的 `FORMALIZATION_STATUS.md`。新英文稿已用输入相关的 Hermitian 分解替代固定酉矩阵路线，因而全局候选证明不再需要 Hastings、Ricard 和 S1 对偶桥梁。固定 Lean 4.30.0-rc1 缓存已恢复，新模块也已在该版本实际构建通过；Riccati、矩形剪切与统一核心范数界已有真实 Lean 证明。

2026-09-05。本文记录实际搜索、源码阅读和已执行的检查。**候选 informal 证明尚未整体形式化；下列条件式引理不能当作原命题的 Lean 证书。** 本轮没有通过添加 Hastings、Ricard、MSS 或主命题公理来制造一个“编译完成”的结论。

## 1. 版本与搜索范围

- 原仓库：`/Users/tsuki/Desktop/CommutatorTheorem`，`lean-toolchain` 为 `leanprover/lean4:v4.30.0-rc1`，默认入口只导入 `CommutatorTheorem.Epsilon.Main`。
- 新隔离项目：本文所在目录。已确认其 mathlib 源码提交为 `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`，对应所需的 4.30.0-rc1。
- 辅助检索：`/Users/tsuki/Desktop/MechGeoBench/.lake/packages/mathlib`（4.27.0），以及 `/Users/tsuki/Desktop/formal-conjectures/.lake/packages/mathlib`（4.33.1）。也检索了 formal-conjectures 自身的 `.lean` 文件。
- 在新项目固定版本再次检索 Hastings、Ricard、Schatten、Mazur map、hollowization、Steinitz lemma、Spielman、Srivastava、Toeplitz–Hausdorff、numericalRange、quantum expander，未找到对应深定理声明。这里的准确结论是**在已检索源码中尚未定位到可直接调用的证明**，不是对全部外部 Lean 项目作不存在性断言。

名字相近的 Gelfand–Mazur、Mazur–Ulam，以及域论的 Steinitz 定理，都不是本证明所需内容。

## 2. 原仓库实际已有的基础

原仓库的 `CommutatorTheorem/Defs.lean` 提供：

- `matComm` 与 `ZeroDiag`。
- 明确启用的 `Matrix.instL2OpNormedAddCommGroup`、`Matrix.instL2OpNormedRing`，以及 `matOpNorm_eq_clm_norm`。必须继续使用这个 Euclidean operator norm；不能误用矩阵按元素的默认范数。
- `hsNorm`、`le_hsNorm`、`hsNorm_le_sqrt_n_mul_opNorm`。后一个含有 `sqrt n`，不能拿来替代候选证明中的维数无关 S1 转换。
- `submatrix_norm_le`、`cross_submatrix_norm_le` 和分块范数基础。

`Epsilon/Main.lean` 的 `fillmore`（源码约第 1672 行）提供迹零矩阵的酉零对角化。该文件还含有私有的 `zero_mem_numerical_range`、`numerical_range_zero_of_trace_zero`；私有声明不能直接当作稳定公共 API 导入。

`Epsilon/THConvexity.lean` 中的 `segment_diag_in_nr_2x2` 是二维数值域线段引理。它是普通数值域证明的可复用组件，但不是高迹质量压缩圆盘定理，也不是三个 Hermitian 矩阵的联合零对角化。

`Epsilon/Rosenblum.lean` 中已有 `rosenblum_solution`、`sylvester_diag_diag_solution`、`sylvester_diag_diag_opNorm_bound` 等。现有不少结论要求两边矩阵对角且同尺寸。新证明需要矩形块与非正规扰动的 Neumann 逆，不能不核对签名就直接调用。

## 3. 逐项依赖表

| 候选证明部分 | 实际可复用内容 | 尚未完成的精确工作 |
| --- | --- | --- |
| §2 Hastings 两酉统一谱隙 | mathlib 的酉群、矩阵 Hilbert 空间、Haar 测度、有限维谱理论 | 未定位到量子扩张子存在定理。需要形式化一个真正维数统一的双酉谱隙存在证明；只有每个固定维数的正谱隙不足以推出统一常数。 |
| §2 Ricard 的有限矩阵 p=1,q=2 Mazur 估计 | 正算子平方根/连续函数演算、有限维谱定理、奇异值基础 | 未定位到 Schatten S1/S2 Mazur Hölder 定理。只需本证明的有限矩阵端点，不必先形式化整篇任意 von Neumann 代数版本；但端点估计本身仍需证明。 |
| §2 S1 商空间谱隙到算子范数求解 | `Analysis/LocallyConvex/Separation.lean` 的 `geometric_hahn_banach_closed_point` 等，有限维紧致性和线性对偶 | 需要定义/连接矩阵迹范数，证明 S∞ 的迹配对对偶、迹零子空间的对偶等于 S1/CI，以及 max 范数直积的对偶为两迹范数之和。已写 informal 推导尚不是 Lean lemma。 |
| §3 Riccati 不动点与单交换子 | `Topology/MetricSpace/Contracting.lean`：`ContractingWith.exists_fixedPoint`、`exists_fixedPoint'`；矩阵块运算、非交换代数恒等式 | 需要证明闭球保留、精确 Lipschitz 常数、因子定义与四块恒等式，并连接上项的两个交换子求解。代数核可独立先做，不能把两个交换子求解默认为已证。 |
| §4 有限次块剪切 | `Matrix.fromBlocks`、块乘法、迹循环、范数次乘性、等距嵌入 | 需要处理不同块尺寸、剪切逆矩阵、二阶项位置、之前零块保持、条件数递推和最终相似返回。现有同尺寸分块代码只是基础。 |
| §5 HM 的圆盘保留 | `Analysis/Matrix/Spectrum.lean` 的 `Matrix.IsHermitian.spectral_theorem`、`trace_eq_sum_eigenvalues`；`InnerProductSpace/Rayleigh.lean`；原仓库数值域组件 | 需要有序谱/压缩极小极大界、普通数值域凸性与支撑半平面表示，继而证明删去 d≤tn/4 维仍含半径 t/4 的圆盘。原仓库“迹零数值域含零”不能直接替代这个较强结论。 |
| §5 密度矩阵极点秩一 | `Analysis/Convex/KreinMilman.lean` 的 `IsCompact.extremePoints_nonempty`，极点/紧致性 API，Hermitian 有限实维数 | 需要证明三个实仿射约束下 PSD 密度矩阵可行集的紧致性，以及秩≥2 时支撑上存在保持三个约束的小扰动。还须在最大值面上选极点并证明其为原集合极点。 |
| §5 正交选择与可逆桥 | 正交投影、子空间余维、标准正交基、奇异值/单射等价等基础；原仓库 `BTPrerequisites` 的投影范数界 | 需要正式构造 r=ceil(tn/16) 个向量，逐步排除 v、Av、A*v、A*Av 四类方向，并证明完整 Av_i 两两正交。尚无该选择定理。 |
| §6 二维 Steinitz 重排 | 有限和、置换、实二维空间、部分和范数基础 | 未定位到所需一般范数 Steinitz 重排界。域论同名定理无关。需要真正证明部分和 l∞≤2 的重排。 |
| §6 三 Hermitian hollowization | 单矩阵 `fillmore`、二维数值域线段基础 | 未定位到 Damm–Faßbender Proposition 13(b)。两矩阵对角恒定、第三个仅末两项偏离以及由 PSD 得到逐向量权重≤2均值，都需独立实现。 |
| §6 MSS 任意 ε 的随机向量选择 | 原仓库已有 real-stability、混合行列式、interlacing tree 和有限随机选择基础，见下节 | 尚未定位到正好满足“独立有限支撑向量、协方差和≤I、期望平方范数≤ε”的 MSS Theorem 1.4 接口。已有 BT 主压缩选择不等于此定理。 |
| §6 每组配额二分与全横截面 | Finset/有限家族和既有有限选择组件 | 在 MSS 接口证明以后，仍需形式化四值成对随机向量的协方差、两个互补半份同时受控，以及 h 层维持每组等配额。不能只证明存在单个横截面就声称全覆盖。 |
| §7 非正规有限块装配 | 原仓库范数/子矩阵/对角 Sylvester 基础；Banach 代数几何级数基础 | 新接口必须允许不同尺寸、非正规子首因子，并严格使用固定标量间距与扰动≤1/2；还需零对角块和实二维网格常数预算。 |
| §8 强归纳和常数闭合 | Lean 的 `Nat.strong_induction_on`，有序实数算术，`norm_num`、`ring`、`linarith` | 本轮已新增并验证抽象归纳核和给定常数的标量闭合，详见第 6 节。尚未把矩阵 HM/低质量分块/装配定理实例化到该核。 |

## 4. 旧 BT / 混合行列式证明能复用到什么程度

源仓库确实包含较多证明，不应因历史注释写着 “sorry” 就将它们全部视作空壳：

- `BTMDPSelection.lean` 的 `DeletionInterlacingTree.select_subset`、`PrefixMDPInterlacing.select_coloring`。
- `BTMDPStability.lean` 的特征多项式导数恒等式，以及从公共交错得到选择的接口。
- `BTRSClosedAssembly.lean` 的 `exactMDPRealRootedness`、`fourHermitianUpperSelection24`、`bourgainTzafriri`。
- `BTAutomationHarness.lean` 中 `rootMotionGoal` 与 `fellConverseGoal` 目前是用已有证明项定义的 `theorem`。
- `BourgainTzafriri.lean` 的 `bourgain_tzafriri_central_submatrix` 调用这两个 theorem，并继续证明 `bourgain_tzafriri_iterated`。

然而，这些结论的主要对象是主子矩阵/坐标着色及 mixed-determinantal polynomial。候选证明所需的 MSS 独立随机向量上界、任意 ε、组内配额二分不是同一个声明。能复用底层实稳定性技术，不代表新的 MSS 应用已被 Lean 验证。

## 5. sorry 与公理审查的实际结果

对原仓库运行了 lean4 skill 的 `lean4-skills-sorry-analyzer`：

```text
Sorry Summary: 0 total across 0 file(s) with sorries; 68 file(s) scanned
```

另对原仓库 `.lean` 搜索了 `axiom`、`sorryAx`、`unsafe`、`implemented_by`。没有定位到新的顶层公理声明或这些实现逃逸。原文件仍有一些“尚余 sorry”“axiom”等历史注释；它们不是当前 live placeholder。

**这个源码检查不是依赖闭包的 kernel 公理证书。** 原仓库的 `AxiomAudit.lean` 已列出主要 epsilon 定理的 `#print axioms`，但必须在固定 4.30rc1 环境实际编译/执行后才能报告那些输出；本文不把文件里写着 `#print axioms` 当作已经得到结果。

还有一个确切入口问题：`Epsilon/FormalizationHarness.lean` 第 37 行导入 `CommutatorTheorem.CommutatorConjecture`，而本次源码文件清单没有该文件。默认入口经 `Epsilon.Main`，因此这是额外 harness 的缺失导入，不能与默认入口构建结果混淆。

## 6. 本轮已实际新增和验证的归纳核

文件：`CommutatorTheorem/NoEpsilon/Induction.lean`。

`uniform_bound_of_shrinking_split` 的 contract 明确给出：

1. 按自然数维数分级的对象、非负 size、随预算单调的 Solution。
2. 每个对象要么有预算 H·size 的直接解，要么有有限个严格小维子对象。
3. 子对象 size≤q·父 size，并具有把统一子预算 p 装配成 c·p+b·父 size 的**局部规则**。
4. 0≤K、0≤q、H≤K，以及 c·q·K+b≤K。

该 theorem 实际证明了所有维数的 Solution(K·size)，使用了严格小维归纳和每个子块的 size 收缩。它没有把完整矩阵主定理作为同义假设；但局部规则确实仍是显式前提，故这个 theorem 单独不能证明原矩阵命题。

同时新增：

- `candidate_budget_closes`：验证 K≥2^43 时，65536·(319/2^26)·K+2^42≤K。
- `candidate_global_constant`：验证最大值定义的 K 同时支配高支预算并闭合低支常数。

三条定理已用可立即运行的 Lean 4.27.0 / mathlib 4.27.0 编译，退出码为 0；独立拼接的 `#print axioms` 审计输出全部只有：

```text
[propext, Classical.choice, Quot.sound]
```

无 `sorryAx` 或自定义公理。新项目的最终环境固定为 4.30.0-rc1，因此仍需在该环境复编后再把它计入最终项目验证；4.27.0 的成功不冒充目标版本的构建成功。

## 7. 当前明确边界

已经有真实可复用的矩阵基础、epsilon 路线源码以及新归纳核。尚未有完整无 epsilon 证明的 Lean 依赖闭包。量子扩张子存在性、有限矩阵 Mazur 端点估计、所需 MSS 版本、Steinitz 重排和三 Hermitian hollowization 是目前未定位到可直接复用证明的深输入；HM 几何与有限剪切装配还需要将 informal 的新连接步骤逐个形式化。

可以把这些精确声明作为明确标注的条件式开发接口，使下游代数、范数、归纳先行编译；但只有逐个解除这些前提，并对最终原命题执行完整构建与 `#print axioms`，才构成用户要求的完整形式化证明。
