# MSS 选择步骤的源码审计与形式化进展

2026-09-05；Lean `v4.30.0-rc1`，mathlib `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`。

**完整有限 MSS、协方差上界扩展、配对选择、低迹质量分支及最终无条件主定理均已形式化完成。** 已补上有限配对概率、奇异基矩阵上的 rank-one 期望行列式恒等式、MSS 多变量差分算子的稳定性，以及完整定量屏障和实际 PSD 矩阵的最优根界。没有引入 MSS、low paving 或主定理的自定义公理；没有 `sorry`。下面区分已经证明的内容和仍需证明的内容。

## 本轮已完成的实际 Lean 声明

### `NoEpsilon/MSSSelection.lean`

- `paired_covariance`：四个 `sqrt 2` 缩放的配对向量，其平均 covariance 恰为两个相同的对角块，交叉项完全抵消。
- `paired_energy`、`paired_energy_le`：每个局部结果的平方 Euclidean 范数等于 `2 (energy a + energy b)`，从而至多 `4 δ`。`energy_eq_euclidean_norm_sq` 将有限平方和与真正 Euclidean 范数连接。
- `paired_total_covariance`、`paired_covariance_deficit`：对所有 pair 求和后的协方差，以及总协方差不超过 `L I` 的 PSD deficit 表述。
- `paired_first_block`、`paired_second_block`：每个实际结果的两个对角块，分别等于两个互补半份 frame operator 的两倍。
- `firstIndices_card`、`secondIndices_card`、`paired_index_partition`：对任意 pair 标签集合，两半各有同样数量的标签，互不相交，且覆盖原来的所有标签。把标签集合取为某个原始组中的 pairs，得到该组的精确一半配额；零向量及重复向量值不会丢失标签。
- `diagonal_blocks_norm_le`、`paired_children_bound_of_outcome`：Euclidean 算子范数下的对角压缩界；**后一条显式假设给定结果的总算子范数至多 `T`**，然后证明两半各至多 `T/2`。它不提供该结果的存在性。
- `pairLaw`、`choiceLaw`、`choiceLaw_eq_uniform`、`paired_vectors_independent`：真实有限概率空间及不同 pair 的独立性。
- `paired_covariance_expectation`、`paired_energy_expectation_le`：上述有限平均是实际 Bochner 积分协方差及期望平方范数，不只是形式符号。

### `NoEpsilon/MixedCharacteristic.lean`

- `det_add_vecMulVec`：对任意交换环及任意有限维矩阵，证明
  `det(A + u vᵀ) = det A + Σᵢ uᵢ det(updateRow A i v)`。
  **允许 A 奇异。** 通过逐行删除 rank-one 更新证明，未使用可逆性假设。
- `firstVariation`：行列式一阶变化量是矩阵扰动的真正线性映射。
- `weighted_rank_one_expected_determinant_sub`：权重和为一时，rank-one 随机减项的期望行列式等于 `det A` 减去平均 rank-one 矩阵的一阶变化量。环可以本身就是其他变量的多项式环。
- `pderiv_det_eq_sum_updateCol`：从原仓库已证源码移植的通用多变量 Jacobi 计算，保留完整证明。
- `pderiv_det_eq_firstVariation`、`map_firstVariation`、`eval_zero_pderiv_pencil_det`：连接多变量导数、线性一阶变化量与系数环求值。
- `weighted_rank_one_mixed_characteristic_step`：完整证明单步 MSS 恒等式
  `Σω pω det(A − uω vωᵀ) = eval₀ ((1 − ∂ₓ) det(A + Xₓ B))`，
  其中 `B = Σω pω uω vωᵀ`。没有把任何选择结论作为前提。
- `firstVariation_one`、`firstVariation_smul_one`、`firstVariation_scalar_ratio`：标量矩阵起点处的初始 logarithmic derivative 是 `trace B / t`。

### `NoEpsilon/MSSStability.lean`

- `UpperStable` 的定义是：所有变量位于开上半平面时，多项式求值非零。
- affine-line 限制及其导数计算从原仓库 `BTStableLine.lean` 移植，保留显式证明。
- `stableLine_logDerivative_ne_one`：新增严格对数导数论证。常数多项式单独处理；非恒定限制的全部根严格在下半平面，因此对数导数的虚部严格为负，不能等于一。
- `UpperStable.sub_nonnegativeDirectionalDerivative`、`UpperStable.sub_pderiv`、`UpperStable.fold_sub_pderiv`：真正证明 MSS 的 `1 − ∂` 稳定性闭包及有限迭代，不假设交错或选择。
- `det_psd_pencil_ne_zero`、`psdPencil_upperStable`：各系数 PSD、总系数正定时，`det(Σᵢ Xᵢ Aᵢ)` 上半平面稳定。这处理任意 PSD 系数矩阵，不仅是旧 BT 的 `det(diag X − H)`。
- `psdPencil_fold_sub_pderiv_upperStable`：PSD pencil 经过有限次 MSS 算子后仍稳定。
- `pderiv_psdPencil`、`eval_pderiv_psdPencil`、`psdPencil_initial_logDerivative`：总 covariance 等于 `I` 时，在所有坐标为非零 `t` 的起点，屏障坐标严格等于 `trace(Aᵢ)/t`。

### `NoEpsilon/MSSPadding.lean`（新增，已编译）

- `exists_outer_decomposition`：通过 PSD 平方根的列向量，实际证明任意有限 PSD 矩阵是有限个向量 outer product 之和。
- `exists_small_energy_decomposition`：给定任意正 `ε`，把每列重复 `K` 次并乘 `1/√K`，得到完全相同的总 covariance 且每个向量能量至多 `ε`。`K` 来自真实 Archimedean 存在性，未假设谱分解或填充接口。
- `norm_le_norm_add_of_posSemidef`：在矩阵 L2 算子范数下，丢弃正半定加项不会增大范数。
- **`finite_mss_le`**：调用已经证明的 `MSSFinite.finite_mss`，为 deficit `I−Σ covariance` 构造上述确定性填充，并删去它，得到任意有限复随机向量、各期望能量至多 `ε>0`、总 covariance `≤ I` 时，存在实际有限结果使总 outer sum 的 L2 范数至多 `(1+√ε)^2`。空原索引和空 ambient 也被覆盖。没有把选择存在性作为前提。

### 完整定量 MSS 屏障与矩阵根界（新增，已编译）

以下各步有完整证明，最终定理没有把单调性、凸性、Pick 表示或根界作为额外假设。

- `MSSBarrier.mixedBarrierDerivative_nonpos`、`barrier_antitone_aboveRoots`：从实际实稳定性推出交叉导数非正以及整个上方正交区域上的屏障单调性。
- `MSSPick.upperStable_of_logDerivative_sign`：通过根重数的 Laurent 极限，证明对数导数上半平面虚部符号强制多项式无上半平面根。
- `MSSSpecialization.coordinatePolynomial_splits`：把其他坐标全部固定为实数，非零的一元限制仍全部实根；`barrier_nonneg`、`barrier_quotient_natDegree_le` 给出屏障非负和有理商次数界。
- `MSSPick.simple_pole_of_laurent_limit`、`MSSResidues.denominator_separable`：从 Pick 符号证明约分后的实极点只能为单极点，残数严格为正。
- `MSSCrossBarrier.exists_barrier_residue_expansion`、`barrier_coordinate_tangent`：通过真实 gcd 约分、Lagrange 部分分式和正残数，得到有限正残数表示与准确的凸性切线不等式。
- `MSSBarrierStep.quantitative_barrier_step`：完整 MSS §5.10；若 `Φⱼ(z) ≤ 1−1/δ`，则 `(1−∂ⱼ)p` 在 `z+δeⱼ` 上方为正，所有新的屏障不超过原值。
- `MSSBarrierIteration.aboveRoots_fold_optimized`：有限次迭代，并实际验证 `t=ε+√ε`、`δ=1+√ε` 得到最优阈值 `(1+√ε)^2`。
- **`MSSPencilBarrier.psdPencil_fold_eval_ne_zero`**：只假设有限 PSD 矩阵 `Aᵢ`、`Σᵢ Aᵢ=I`、`trace Aᵢ≤ε` 和 `ε>0`，证明真实复系数 mixed differential polynomial 在每个实数 `x≥(1+√ε)^2` 的对角求值非零。这已经是 MSS 所需的实际确定性根界。

上述证明还调用已完整证明的 `MSSPartialFractions`、`MSSReducedFraction`、`MSSResidueBounds`、`MSSBarrierAlgebra` 和 `MSSRealPencil` 辅助模块。没有引入自定义公理。

## 原仓库实际可复用的内容

源码目录：`/Users/tsuki/Desktop/CommutatorTheorem/CommutatorTheorem/Epsilon/`。

| 文件和声明 | 实际覆盖范围 | 与所需 MSS 的差别 |
| --- | --- | --- |
| `BTDeterminantStability.lean:112`，`hermitianDetPoly_complexStable` | `det(diag z − H)` 的稳定性 | 原声明不是任意 PSD 系数 pencil；本轮已补上后一种情形。 |
| `BTHermitianDetPDeriv.lean:18`、`:60` | 有限乘积求导及任意矩阵多项式的 Jacobi 公式 | 已移植并用于新的 rank-one 期望恒等式。 |
| `BTStableLine.lean` | 多变量多项式的 affine-line 限制、导数、根位于下半平面及弱虚部符号 | 已移植所需部分，并新增严格不等于一，从而证明 MSS 差分算子闭包。 |
| `BTGaussLucasHurwitz.lean:26`，`multivariateGaussLucasHurwitz` | 非负方向导数的稳定或零闭包 | 原文件有证明；它不是 MSS 定量 barrier theorem。 |
| `BTInterlacing.lean:1328`，`HasCommonInterlacer.exists_largestRoot_and_member_below_of_realRooted` | 给定共同交错因子的有限多项式选择 | 可用于最终选择，但仍需为新的独立 rank-one 条件期望多项式建立具体交错树并装配。 |
| `BTFellCountInduction.lean:302` | 任意次数的 root-disjoint Fell converse | 是已证源码，不必重新假设；仍需连接新的 mixed characteristic family。 |
| `BTRootShrinkingClose.lean:142`，`derivativeBarrierStep_of_realRooted` | 一元 `p → p'` 后向左移动的 barrier | 与 MSS 的多变量 `p → (1−∂ᵢ)p`、向正坐标移动不同，不能直接套用。 |
| `BTMDPSelection.lean`、`BTRSExactMDPHarness.lean` | 主压缩/坐标着色 deletion tree 和 exact mixed-determinantal polynomial | 对象、有限选择树和参数界均不是 MSS Thm. 1.4 的独立随机 rank-one 选择。 |
| `BTAutomationHarness.lean` | 已从闭合的一元 root-motion 和 Fell 定理装配 BT 路线 | 它不提供本任务的任意 ε、精确组配额的 MSS 选择接口。 |

本轮已实际搜索 mathlib 与原仓库中的 MSS、Marcus、mixed-characteristic、rank-one expectation 等相关关键词，并阅读上述具体声明和证明。结论是“没有找到可直接调用的所需完整接口，且实际读到的 BT 定理类型不同”；不是从关键词无结果推断所有可能证明在数学上不存在。原仓库没有对应本次环境可直接使用的已编译 `.olean` 目录，本轮对原仓库是源码审计；新移植及新证明均在隔离项目中重新编译。

## 最终连接状态

`MSSScaled.finite_mss_scaled` 和 `LowMassPaving.pairedHalfSelection` 现已由协作代理完成真实编译及公理审计，均仅依赖标准三项公理。它们覆盖 `L≥0`、`ε≥0`，包括两个零参数端点；有限结果的最小代价选择结合连续极限严格处理边界。由此低质量组配额二叉树的 analytic premise 已成为无条件定理。

当前 MSS 选择、任意标量 covariance 上界、确定性 deficit 填充、配对精确半份选择都已闭合。全项目最终入口 `NoEpsilon.Main` 现已真实构建成功（8393 jobs）。最终 `uniformCommutatorBound` 及其展开 Euclidean 算子范数版本的独立完整公理审计也已通过，仅依赖标准三项；详见 `FINAL_SEMANTICS_AUDIT.md`。

## 编译与公理审计

执行：

```
/Users/tsuki/.elan/toolchains/leanprover--lean4---v4.30.0-rc1/bin/lake build NoEpsilon.MSSPadding
```

该入口包含完整有限选择、定量屏障、实际矩阵起点及 deficit 填充，构建成功（8312 jobs）。`MSSSelection` 和 `MixedCharacteristic` 也已独立编译。关键声明已执行 `#print axioms`，结果只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`、MSS 或其他自定义公理。共享 `NoEpsilon.lean` 与 `AxiomAudit.lean` 留给父代理集成。
