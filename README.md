# A dimension-independent commutator bound via trace-mass splitting

Lean 4 formalizations of two commutator theorems for traceless complex matrices.
All norms below are Euclidean operator norms, and both factors have the same size as the input.

## Paper–code correspondence

| Paper | Main result | Lean theorem |
|---|---|---|
| *A dimension-independent commutator bound via trace-mass splitting*, Theorem 1.1 | There is a universal $K > 0$ such that $A = BC - CB$ and $\|B\|\,\|C\| \le K\|A\|$. No normality assumption is imposed on the factors. | [NoEpsilon.uniformCommutatorBound](CommutatorTheorem/NoEpsilon/Main.lean) |
| Johnson–Ozawa–Schechtman, *A quantitative version of the commutator theorem for zero trace matrices*, Theorem 1 (PNAS, 2013; local reference: `epsilon.pdf`; DOI: `10.1073/pnas.1201411109`) | For every $\varepsilon > 0$, there is $K_\varepsilon > 0$ such that $A = BC - CB$, $B$ is normal, and $\|B\|\,\|C\| \le K_\varepsilon n^\varepsilon\|A\|$. | [CommutatorTheorem.main_commutator_theorem_normal](CommutatorTheorem/Epsilon/Main.lean) |

In the first row, $K$ is chosen before the dimension $n$ and matrix $A$; in the second,
$K_\varepsilon$ depends only on $\varepsilon$. Both statements apply to every traceless
complex $n \times n$ matrix. The explicit operator-norm version of the first theorem is
[NoEpsilon.uniformCommutatorBound_euclideanOperatorNorm](CommutatorTheorem/NoEpsilon/Main.lean).

The two proofs live in [NoEpsilon](CommutatorTheorem/NoEpsilon) and
[Epsilon](CommutatorTheorem/Epsilon), with shared unitary zero-diagonalization in
[Shared/Fillmore.lean](CommutatorTheorem/Shared/Fillmore.lean).
The repository also contains the accompanying [paving separation results](PavingSeparation).
The following gives a one-to-one correspondence between the paper's theorems and the Lean code. The statements labeled **Theorem** are aligned with the paper. The **Lemma** and **Proposition** statements are not yet fully aligned because of some technical gaps, but they are broadly aligned overall.

## Build and verify

Install Lean's `elan` toolchain manager, then run the following commands from the repository root:

```sh
lake exe cache get
lake build
```

The toolchain is pinned to **Lean 4.30.0-rc1** in [lean-toolchain](lean-toolchain), and the mathlib revision is pinned in [lake-manifest.json](lake-manifest.json). The default build compiles both `CommutatorTheorem` and `PavingSeparation`.

After building, check the paper correspondence and the main theorem:

```sh
lake env lean PaperCorrespondence.lean
lake env lean CommutatorTheorem/NoEpsilon/FinalVerification.lean
```

These checks resolve the indexed declarations and print the axioms of key results. The expected axioms are `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`. For the unified audit of both the Epsilon and NoEpsilon branches:

```sh
lake env lean AxiomAudit.lean
```

## License

Copyright (c) 2026 lean-commutator contributors.

This project's Lean source code is licensed under the [Apache License 2.0](LICENSE). Dependencies retain their own licenses.
