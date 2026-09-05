# 无 epsilon 定理：完整证明已通过 Lean 检查

更新：2026-09-05。本记录取代此前所有“尚未完成”的进度快照。

## 已证明的结论

存在与维数无关的实常数 `K > 0`，使每个复迹零矩阵 `A : Matrix (Fin n) (Fin n) ℂ` 都有同维矩阵 `B,C` 满足

\[
A=BC-CB,\qquad \|B\|\|C\|\le K\|A\|.
\]

所有范数均为欧几里得算子范数。结论包括所有自然数维数，没有扩大矩阵维数，没有 `n^ε` 因子。此结论不要求第一因子正规。

完整入口为 `NoEpsilon/Main.lean`：

```lean
theorem uniformCommutatorBound : UniformCommutatorBound
```

这个定理没有额外参数或待提供的数学假设。`lowMassPavingInput_proved` 已把归纳中的低质量铺砌输入完全实例化。`uniformCommutatorBound_euclideanOperatorNorm` 使用 `Matrix.toEuclideanCLM` 的实际算子范数展开了完整结论。

## 最终验证证据

- `lake build NoEpsilon.Main` 成功：完整高质量分支、完整低质量分支及全局归纳均编译。
- 统一验证脚本成功审计 **91 个声明**，包含完整主定理。
- `NoEpsilon/FinalVerification.lean` 直接检查展开后的原始量词与同维结论，并以 `rfl` 核对矩阵范数等于 `Matrix.toEuclideanCLM` 的算子范数。
- 主定理完整公理依赖恰为 `[propext, Classical.choice, Quot.sound]`，没有 `sorryAx` 或自定义数学公理。
- 另一个代理独立检查了量词、范数、维数保持及最终公理依赖；见 `FINAL_SEMANTICS_AUDIT.md` 和 `FINAL_INDEPENDENT_AXIOM_AUDIT.txt`。

原始验证输出、时间、声明清单和源文件摘要保存在 `verification/`。其中 `results.json` 的 `full_UniformCommutatorBound_proved` 为 `true`；只有构建、展开声明检查及主定理完整公理审计全部成功，脚本才会写入这一结果。

## 证明的完整连接

1. Hermitian 单交换子、两个有界交换子的自适应分解、Riccati 不动点给出单位交叉块核心。
2. 高迹质量条件产生正交中性帧与定量可逆交叉块；有限次剪切消去外部对角块，经 Sylvester 装配与相似变换还原，得到完整高质量分支。
3. 二维 Steinitz 排列、精确谱分组及三个 Hermitian 矩阵的共同基给出低质量分支的框架。
4. 完整 MSS 证明包含稳定性、实特化、残数与屏障估计、优化迭代、期望特征多项式、交错选择、真实结果选择、协方差补足和缩放。没有把 MSS 或好结果存在性当作公理。
5. 配对选择与精确配额树给出完整正交铺砌，保持每块迹零，范数至多 `319 / 2^26`。
6. 全局强归纳处理零矩阵、空维数、小维数和非整除维数。令 `R=2^26`，单次装配的收缩系数为 `65536·319/R=319/1024<1/2`；所有余坐标作为单独零对角块保留。

`GlobalInduction.lean` 给出显式有限常数 `globalNormBudget`。它极大，证明并未优化常数。

## 复核

工具链：`leanprover/lean4:v4.30.0-rc1`。

mathlib 固定提交：`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`。

在项目目录运行：

```sh
python3 scripts/verify_no_epsilon.py --lake /absolute/path/to/pinned/lake
```

原始 `/Users/tsuki/Desktop/CommutatorTheorem` 未修改。本目录保存完成的形式化与验证记录。匿名英文论文及源文件在本目录的 `paper/` 子目录；尚未提交 arXiv。
