# A dimension-independent single-commutator bound

This project proves that there is a universal `K > 0` such that every trace-zero
complex `n × n` matrix satisfies

\[
A=BC-CB,\qquad \|B\|\|C\|\le K\|A\|,
\]

where both factors are `n × n` and all norms are Euclidean operator norms.
The constant is independent of `n`. The first factor is not required to be normal.

The complete theorem is `NoEpsilon.uniformCommutatorBound` in
`NoEpsilon/Main.lean`. It has no additional parameters or mathematical assumptions.
`NoEpsilon/FinalVerification.lean` checks the expanded statement and norm
interpretation. The full axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or additional mathematical axiom.

## Verification

The toolchain is pinned to Lean `4.30.0-rc1`; `lake-manifest.json` pins mathlib to
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`.

```sh
lake build NoEpsilon
lake env lean NoEpsilon/FinalVerification.lean
python3 scripts/verify_no_epsilon.py --lake /absolute/path/to/pinned/lake
```

The last command audits 91 declarations, including the complete main theorem,
and writes raw logs and the machine-readable result to `verification/`.
See `FORMALIZATION_STATUS.md` for the Chinese completion report and
`FINAL_SEMANTICS_AUDIT.md` for the independent semantic audit.

## Proof organization

- `HighMassTheorem.lean`: the complete high trace-mass branch.
- `MSSFinite.lean`, `MSSPadding.lean`, `MSSScaled.lean`, `MSSPaired.lean`: the full
  finite complex vector-selection theorem and exact paired selection.
- `LowMassTheorem.lean`: complete trace-preserving equal-rank paving.
- `GlobalAssembly.lean`, `GlobalReduction.lean`, `GlobalInduction.lean`: single-step
  assembly, normalization, residual dimensions, and strong induction.
- `Main.lean`: the unconditional dimension-independent theorem.

These filenames are under `NoEpsilon/`. The anonymous paper and LaTeX source
are included in `paper/`. It has not been submitted to arXiv.

The original epsilon-dependent formalization remains under `CommutatorTheorem/`.
The original desktop project was not modified. This is an independent desktop
copy containing sources and all pinned mathlib dependencies in `.lake/packages`.
Both `CommutatorTheorem` and `NoEpsilon` are default targets, so `lake build`
checks the completed theorem. See `README_DESKTOP_CN.md` for local instructions.
