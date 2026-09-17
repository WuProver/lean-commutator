# Explicit commutator bound: 2^3200

The exact strengthened theorem is `NoEpsilon.commutator_bound_two_pow_3200`.
Its only mathematical hypothesis is `Matrix.trace A = 0`. Both factors have the
same matrix type as `A`; the norm is the induced Euclidean operator norm.

From the repository root:

```sh
lake build
lake env lean verification/explicit_3200/Audit.lean
lake env lean AxiomAudit.lean
```

- `build.log`: full default-target build after the final Lean source changes.
- `axioms_and_types.log`: explicit final signatures and transitive axiom sets.
- `full_axioms.log`: the repository's unified axiom audit, including the new results.
- `manifest.json`: Lean/Mathlib versions, source hashes, commands, and outcomes.
- `latex.log`: final PDF compilation log.

The informal proof is `output/pdf/commutator_bound_2pow3200.pdf`; its editable
source is `paper/commutator_bound_2pow3200.tex`. It includes the whole commutator
argument and the new simultaneous-elimination and numerical-estimate proofs.
It does not reproduce the separate paving-separation theorem.

The two new source modules are `SimultaneousAbsorption.lean` and
`ExplicitBound.lean` under `CommutatorTheorem/NoEpsilon/`. The former proves the
actual two-shear matrix construction, not merely the scalar arithmetic. The
existing absorption interface now calls it; the global induction exposes its
actual budget, and the latter module bounds that budget by the literal 2^3200.
Existing existential theorem interfaces are retained.
