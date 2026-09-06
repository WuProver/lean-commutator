# A dimension-independent commutator bound via trace-mass splitting

本 README 是论文与 Lean 源码的核查索引。核对对象为仓库根目录的
[A_dimension_independent_commutator_boundvia_trace_mass_splitting.pdf](A_dimension_independent_commutator_boundvia_trace_mass_splitting.pdf)
（论文日期 2026-09-05，共 15 页），以下页码均指该 PDF。没有用 `paper/main.tex` 的编号替代这份 PDF。

主定理断言存在一个与维数无关的常数 K > 0，使任意无迹复矩阵 A 都有同维度分解

$$
A=BC-CB,\qquad \|B\|\,\|C\|\le K\|A\|.
$$

范数是 Euclidean operator norm；不要求第一因子正规。下面的对应关系来自论文陈述与当前源码声明的逐项阅读；“组合对应”表示需要多个接口，不能仅凭一个同名文件认定陈述完全一致。本文档不是对论文每一行证明的独立数学审稿。

## 编号定理、引理与推论

链接指向声明所在行。所有 13 个编号结果均列于下表；Remark 2.3、7.2 的说明另列在后面。

| 论文位置 | 核查内容 | Lean 声明 | 对应方式与注意点 |
|---|---|---|---|
| Theorem 1.1（p. 2；证明 pp. 12–13） | 同维度、与维数无关的单交换子范数界 | [NoEpsilon.uniformCommutatorBound](CommutatorTheorem/NoEpsilon/Main.lean#L21) | 直接对应；展开命题见下文，Lean 还包括 n = 0。 |
| Lemma 2.1（p. 3） | 无迹 Hermitian 矩阵的酉第一因子交换子分解 | [NoEpsilon.hermitianUnitaryCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean#L179) | 直接对应；完整量词与范数界在 [NoEpsilon.HermitianUnitaryCommutatorBound](CommutatorTheorem/NoEpsilon/HermitianSplit.lean#L81)。 |
| Corollary 2.2（p. 3） | 两个交换子之和，两第一因子均为酉矩阵 | [NoEpsilon.adaptiveTwoCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean#L210) | 直接对应；命题定义为 [NoEpsilon.AdaptiveTwoCommutatorBound](CommutatorTheorem/NoEpsilon/HermitianSplit.lean#L90)。第一因子随输入选择。 |
| Proposition 3.1（pp. 4–5） | 单位角块核心的单交换子表示，预算 P(a) | [NoEpsilon.identityCorner_bounded_from_whole_norm](CommutatorTheorem/NoEpsilon/CoreTheorem.lean#L78) | 直接对应；块索引用 Fin n ⊕ Fin n，P(a) 为 [NoEpsilon.identityCornerNormBudget](CommutatorTheorem/NoEpsilon/NormBounds.lean#L119)。 |
| Lemma 4.1（p. 5） | 分离中心的矩形 Sylvester 方程及分母估计 | [NoEpsilon.exists_sylvester_solution](CommutatorTheorem/NoEpsilon/Sylvester.lean#L88) | 直接对应；双系数写法见 [NoEpsilon.exists_sylvester_solution_scalar_centers](CommutatorTheorem/NoEpsilon/Sylvester.lean#L103)。 |
| Proposition 4.2（pp. 5–7） | 有限次剪切吸收外部对角块并重组 | [NoEpsilon.Absorption.identity_corner_absorption](CommutatorTheorem/NoEpsilon/AbsorptionCore.lean#L76) | 块坐标形式；absorptionBudget 的参数 m 是外部块数，即论文 b − 2。允许空外部块。 |
| Lemma 5.1（p. 7） | 低余维压缩的数值域包含半径 t/4 的圆盘 | [NoEpsilon.highMass_compression_contains_disk](CommutatorTheorem/NoEpsilon/HighMassCompression.lean#L133) | 归一化坐标形式；子空间通过等距矩阵 V 表示，压缩为 VᴴAV。 |
| Lemma 5.2（pp. 7–8） | 数值域含 ±ρ 时存在零期望、像范数至少 ρ 的单位向量 | [NoEpsilon.exists_unit_neutral_large_image_of_numericalRange](CommutatorTheorem/NoEpsilon/HighMassGeometry.lean#L350) | 结论对应，证明不同：Lean 使用两列 Gram 矩阵的零对角化，不是论文的密度矩阵极点证明。 |
| Proposition 5.3（p. 8） | 高迹质量分支的维数无关预算 | [NoEpsilon.highMass_bounded_commutator](CommutatorTheorem/NoEpsilon/HighMassTheorem.lean#L46) | 归一化接口；恢复原范数还需 [NoEpsilon.commutator_of_normalized](CommutatorTheorem/NoEpsilon/GlobalReduction.lean#L41)。常数对应见下文。 |
| Lemma 6.1（p. 9） | H、G 对角为均值，E 的每个对角项不超过两倍均值 | [NoEpsilon.ThreeHermitian.exists_diagonal_control](CommutatorTheorem/NoEpsilon/ThreeHermitianBasis.lean#L245) | 直接对应；以酉矩阵给出基，Lean 还覆盖维数 0、1。第三矩阵只有上界，不要求对角恒定。 |
| Lemma 6.2（pp. 9–10） | 恰好每组取一个索引的 R 个横截集，预算 C_D/R | [NoEpsilon.LowMassPaving.exists_transversals](CommutatorTheorem/NoEpsilon/LowMassTransversals.lean#L163) | 组合对应；需传入已证明的 [NoEpsilon.LowMassPaving.pairedHalfSelection](CommutatorTheorem/NoEpsilon/MSSPaired.lean#L18)。每组一个置换保证精确配额和不重不漏。 |
| Proposition 6.3（pp. 10–11） | 等秩、迹为零、压缩范数 ≤ 319/R 的铺砌 | [NoEpsilon.normalized_low_mass_paving](CommutatorTheorem/NoEpsilon/LowMassTheorem.lean#L39) | 最终接口采用 ¬ HasHighTraceMass；论文的非严格 ≤ 条件需从 [NoEpsilon.LowMassPaving.exists_paving_basis](CommutatorTheorem/NoEpsilon/LowMassBasis.lean#L137) 等底层结果组合，不能把两接口视为字面相同。 |
| Lemma 7.1（pp. 11–12） | 有限块拼装，预算 8s·max pᵢ + b‖A‖ | [NoEpsilon.BlockAssembly.assemble_fixed_constants](CommutatorTheorem/NoEpsilon/BlockAssembly.lean#L310) | 以共同预算 p 代替 max pᵢ，常数为 65536 和 2^42；酉坐标及余数块另见下文。 |

## 主定理、范数语义与全局归纳

- **主定理命题**：[NoEpsilon.UniformCommutatorBound](CommutatorTheorem/NoEpsilon/Goal.lean#L17)。量词顺序为 ∃ K > 0，随后 ∀ n、∀ A；B、C 与 A 使用相同 Fin n 索引。
- **显式算子范数版本**：[NoEpsilon.uniformCommutatorBound_euclideanOperatorNorm](CommutatorTheorem/NoEpsilon/Main.lean#L25)。直接使用 Matrix.toEuclideanCLM 的范数。
- **范数解释的等价性**：[NoEpsilon.uniformCommutatorBound_iff_euclideanOperatorNorm](CommutatorTheorem/NoEpsilon/GoalSemantics.lean#L16)。把 scoped 矩阵范数与 EuclideanSpace 上连续线性算子的范数连接起来。
- **强归纳主体**：[NoEpsilon.uniformCommutatorBound_of_lowMassBlocksAt](CommutatorTheorem/NoEpsilon/GlobalInduction.lean#L58)。这是含铺砌假设的中间归约，不能单独作为无条件主定理。
- **消去最后的铺砌假设**：[NoEpsilon.lowMassPavingInput_proved](CommutatorTheorem/NoEpsilon/Main.lean#L16)。将完整低迹质量定理代入，Main.lean 最终得到无条件主定理。
- **带余数的拼装**：[NoEpsilon.GlobalAssembly.assemble_with_leftovers](CommutatorTheorem/NoEpsilon/GlobalAssembly.lean#L86)。处理 R 个小块及 q 个零对角单点块。
- **高迹质量块与余数的拼装**：[NoEpsilon.assemble_one_with_leftovers](CommutatorTheorem/NoEpsilon/GlobalAssembly.lean#L140)。处理一个已解的大块和 q 个零对角单点块。
- **小维数**：[NoEpsilon.zeroDiag_small_commutator](CommutatorTheorem/NoEpsilon/GlobalReduction.lean#L55)。n < R 时从零对角单点块直接拼装。

## 第 6 节引用的输入与辅助步骤

这些是论文在文字中引用或在证明中使用的结果，不是额外的论文编号定理。

| 论文位置或步骤 | Lean 入口 | 核查内容 |
|---|---|---|
| §6.1 Steinitz 二维重排 | [NoEpsilon.Steinitz.exists_order](CommutatorTheorem/NoEpsilon/Steinitz.lean#L347) | Fin 2 → ℝ 的 sup 范数；每个前缀和范数 ≤ 2。 |
| 式 (6.9) 的连续分组 | [NoEpsilon.SteinitzGrouping.exists_trace_controlled_groups](CommutatorTheorem/NoEpsilon/SteinitzGrouping.lean#L74) | 由前缀差得到每组坐标误差 ≤ 4。 |
| §6.1 Damm–Faßbender hollowisation | [NoEpsilon.ThreeHermitian.exists_almost_hollow](CommutatorTheorem/NoEpsilon/ThreeHermitianBasis.lean#L118) | 前两矩阵对角全零，第三矩阵除最后至多两个位置外为零。 |
| 式 (6.2)–(6.3) MSS 独立向量定理 | [NoEpsilon.MSSFinite.finite_mss](CommutatorTheorem/NoEpsilon/MSSFinite.lean#L137) | 有限概率权重、期望能量条件、总协方差为 I。 |
| 总协方差 ≤ I 的扩展 | [NoEpsilon.MSSPadding.finite_mss_le](CommutatorTheorem/NoEpsilon/MSSPadding.lean#L103) | 构造半正定亏损的确定性填充再去掉填充项。 |
| 式 (6.5)–(6.6) 的配对二分 | [NoEpsilon.LowMassPaving.pairedHalfSelection](CommutatorTheorem/NoEpsilon/MSSPaired.lean#L18)；[NoEpsilon.MSSScaled.finite_mss_scaled](CommutatorTheorem/NoEpsilon/MSSScaled.lean#L91) | 缩放后的 MSS 同时控制两个互补子集。 |
| 式 (6.4) 的树递推 | [NoEpsilon.LowMassPaving.binary_recurrence_leaf_bound](CommutatorTheorem/NoEpsilon/LowMassRecurrence.lean#L55) | 深度 h 时得到 C_D / 2^h。 |
| 319 的数值估计 | [NoEpsilon.LowMassPaving.transversalConstant_twelve_add_four_lt](CommutatorTheorem/NoEpsilon/LowMassRecurrence.lean#L77) | 精确证明 C₁₂ + 4 < 319。 |
| Proposition 3.1 的 Riccati 步骤 | [NoEpsilon.exists_riccati_fixedPoint_large_scale](CommutatorTheorem/NoEpsilon/Riccati.lean#L127) | 大尺度下的固定点存在性；具体块构造见 [IdentityCorner.lean](CommutatorTheorem/NoEpsilon/IdentityCorner.lean) 和 [NormBounds.lean](CommutatorTheorem/NoEpsilon/NormBounds.lean)。 |
| Proposition 4.2 的有限剪切 | [NoEpsilon.Absorption.eliminate_finset](CommutatorTheorem/NoEpsilon/FiniteAbsorption.lean#L326) | 保留单位角块，消掉有限集合内的外部对角块并控制相似变换。 |
| Proposition 5.3 的贪心正交族 | [NoEpsilon.highMass_exists_neutral_frame](CommutatorTheorem/NoEpsilon/HighMassGreedy.lean#L135) | 逐步构造大像范数的 neutral frame。 |
| Proposition 5.3 的比例秩桥 | [NoEpsilon.highMass_exists_diagonal_bridge](CommutatorTheorem/NoEpsilon/HighMassBridge.lean#L99) | 从正交族得到对角桥，后续由 [HighMassCoordinates.lean](CommutatorTheorem/NoEpsilon/HighMassCoordinates.lean) 与 [DiagonalAbsorption.lean](CommutatorTheorem/NoEpsilon/DiagonalAbsorption.lean) 接入吸收。 |

## 常数与陈述差异的核查

1. **式 (3.1)、(4.1)、(4.2)**：P(a) 是 [NoEpsilon.identityCornerNormBudget](CommutatorTheorem/NoEpsilon/NormBounds.lean#L119)；β、f 分别是 [NoEpsilon.Absorption.firstBudget](CommutatorTheorem/NoEpsilon/FiniteAbsorption.lean#L179)、[NoEpsilon.Absorption.stepBudget](CommutatorTheorem/NoEpsilon/FiniteAbsorption.lean#L182)。[NoEpsilon.Absorption.absorptionBudget](CommutatorTheorem/NoEpsilon/AbsorptionCore.lean#L70) 使用 m 个外部块：令 m = b − 2、k = m + 1，展开后就是论文 (4.2) 的预算。
2. **式 (5.1) 的归一化**：[NoEpsilon.HasHighTraceMass](CommutatorTheorem/NoEpsilon/HighMassCompression.lean#L63) 要求每个单位复数旋转的 Hermitian 部分满足“绝对特征值和 ≥ t·n”，右侧没有再乘 ‖A‖。它用于归一化矩阵；不要直接将其等同于任意未归一化 A 的 HM(t)。旋转用单位复数 c 表示，论文用 exp(iθ)。
3. **式 (5.3)**：[NoEpsilon.highMassNormBudget](CommutatorTheorem/NoEpsilon/HighMassTheorem.lean#L19) 写作 `((t / 4)⁻¹)^2 * absorptionBudget ((t / 4)⁻¹) ⌈16 / t⌉₊`。在 t > 0 下展开 absorptionBudget，约去初始尺度的平方，得到论文预算 `a*² · [4(L+1)P(a*) + 2(L+1)²a*]`。这是对定义的代数核对；没有新增单独的 Lean 常数等式定理。
4. **Proposition 6.3 的边界条件**：论文条件是某个旋转的迹质量 **≤ 2k‖A‖**；最终 `normalized_low_mass_paving` 的假设是 **¬ HasHighTraceMass**，归一化后给出某个旋转的迹质量 **< 2k**。底层 `exists_paving_basis` 接受半正定 E 且 **tr E ≤ 2k**，保留了非严格边界，但还需构造 H、G、E、代入已证明的 pairedHalfSelection，再恢复旋转和尺度。当前未找到将论文 (6.7) 原样封装的单独声明；不能把最终接口标成该非严格版本的逐字形式化。铺砌以正交基和 WᴴAW 表示，论文投影由 P = WWᴴ 得到。
5. **式 (7.2)**：[NoEpsilon.globalNormBudget](CommutatorTheorem/NoEpsilon/GlobalInduction.lean#L37) 是 `max (65536 * max (highMassNormBudget (2 / 2^26)) 0 + 2^42) (2^43)`。相较论文多了内部 `max KH 0`，供形式证明直接取得非负性。收缩预算由 [NoEpsilon.globalNormBudget_closes](CommutatorTheorem/NoEpsilon/GlobalInduction.lean#L44) 证明。
6. **Remark 2.3、7.2**：`AdaptiveTwoCommutatorBound` 的量词顺序确为 ∀ A ∃ U,K,V,T；主定理不要求 B 正规。配对向量选择中使用辅助直和空间，但最终交换子 B、C 和 A 始终具有相同矩阵索引类型。

## 如何复核

在仓库根目录运行：

```sh
lake build CommutatorTheorem.NoEpsilon
lake env lean CommutatorTheorem/NoEpsilon/FinalVerification.lean
lake env lean CommutatorTheorem/NoEpsilon/AxiomAudit.lean
```

[FinalVerification.lean](CommutatorTheorem/NoEpsilon/FinalVerification.lean) 展开主定理、检查矩阵范数的定义相等性，并对主定理及显式 Euclidean operator norm 版本执行 `#print axioms`。[AxiomAudit.lean](CommutatorTheorem/NoEpsilon/AxiomAudit.lean) 对多个中间声明执行公理审计。应核对输出是否仅含 `propext`、`Classical.choice`、`Quot.sound`，以及是否出现 `sorryAx` 或其他数学公理。

本次核查（2026-09-06）已运行 `lake env lean CommutatorTheorem/NoEpsilon/FinalVerification.lean`，成功通过；两条主定理的公理输出均为 `[propext, Classical.choice, Quot.sound]`。另以临时 Lean 文件对表中 47 个不同声明逐个执行 `#check`，全部通过，并检查了 60 个本地链接。本次仅修改 README，没有重新运行全库构建或全量中间声明公理审计。

Lean 工具链固定为 `4.30.0-rc1`；mathlib 版本以 [lake-manifest.json](lake-manifest.json) 为准。默认 `lake build` 构建 `CommutatorTheorem` 与 `PavingSeparation` 两个库。

论文主要实现位于 [CommutatorTheorem/NoEpsilon](CommutatorTheorem/NoEpsilon)。部分辅助结果来自 [CommutatorTheorem/Epsilon](CommutatorTheorem/Epsilon)，例如源码使用的零对角化工具；独立的 [PavingSeparation](PavingSeparation) 库不应与本文 §6 的低迹质量铺砌直接按名称混同。

本索引不依赖已被 Git 忽略的 `paper/`、`scripts/`、`verification/` 或历史审计说明文件。文件移动或声明行号变化后，需要更新相应链接。
