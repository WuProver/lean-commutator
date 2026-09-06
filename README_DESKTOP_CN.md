# 桌面独立编译版

此文件夹包含完整 Lean 源码、固定版本的 mathlib 依赖及其缓存、匿名论文。
不需要引用 Codex 输出目录，也没有指向该目录的软链接。

## 使用

在这个文件夹打开终端运行：

```sh
lake build
python3 scripts/verify_no_epsilon.py
```

也可以双击 `compile.command` 完成构建与公理审计。

`lake build` 默认同时构建 `CommutatorTheorem` 和 `PavingSeparation` 两个库，共用根目录 `.lake`。
单独构建 `PavingSeparation` 可运行 `lake build PavingSeparation`。
完整主定理在 `CommutatorTheorem/NoEpsilon/Main.lean`，名称为 `NoEpsilon.uniformCommutatorBound`。
论文 PDF 和 LaTeX 在 `paper/`。

## 环境

- Lean：`leanprover/lean4:v4.30.0-rc1`，已安装在当前电脑。
- mathlib：`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`。
- `.lake/packages` 是独立文件副本，包含依赖的源码、Git 元数据和编译缓存。
- 没有复制原项目的 `.lake/build`；桌面项目自身的源码会重新编译。
- 复制到其他平台需要安装相应 Lean 工具链，并重新取得该平台的依赖缓存。

本目录的最新验证记录写入 `verification/`。原 Codex 验证快照保留在
`verification/prior_codex/`，以免与本次桌面编译混淆。

## 本次实际验证

桌面项目已在没有旧项目编译缓存的条件下，通过默认双库构建。
双击脚本也已实际运行成功：主定理、展开后的欧几里得算子范数版本及
91 个声明的公理审计均通过。142 个 Lean 源文件保持原样。
导入路径不包含 Codex 目录，依赖内部的相对软链接也没有离开本文件夹。

机器可读记录：`verification/desktop_verified.json`。
完整构建日志：`verification/desktop_build.log`。
完整验证脚本日志：`verification/desktop_verify.log`。
