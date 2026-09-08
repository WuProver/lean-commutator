# A dimension-independent commutator bound via trace-mass splitting

Lean 4 formalizations of two commutator theorems for traceless complex matrices.
All norms below are Euclidean operator norms, and both factors have the same size as the input.

## Main theorem correspondence
The following gives a one-to-one correspondence between the paper's theorems and the Lean code. The statements labeled **Theorem** are aligned with the paper. The **Lemma** and **Proposition** statements are not yet fully aligned because of some technical gaps, but they are broadly aligned overall.

| Paper result | Content | Lean entry point |
|---|---|---|
| Theorem 1.1 | Dimension-independent commutator bound. | [NoEpsilon.uniformCommutatorBound](CommutatorTheorem/NoEpsilon/Main.lean) |
| Theorem 1.4 | Exact paving and normal-factor cost, including the square-normalized λ lower bound. | [PavingSeparation.paving_commutator_separation](PavingSeparation/Theorem1.lean); [PavingSeparation.finFamily_lambdaA_lower_bound](PavingSeparation/Lambda.lean) |
| Lemma 2.1 | Hermitian commutator decomposition with a unitary first factor. | [NoEpsilon.hermitianUnitaryCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean) |
| Corollary 2.2 | Sum of two commutators with unitary first factors. | [NoEpsilon.adaptiveTwoCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean) |
| Lemma 3.1 | Identity-corner commutator representation. | [NoEpsilon.identityCorner_bounded_from_whole_norm](CommutatorTheorem/NoEpsilon/CoreTheorem.lean) |
| Lemma 3.2 | Rectangular Sylvester equation with separated scalar centers. | [NoEpsilon.exists_sylvester_solution](CommutatorTheorem/NoEpsilon/Sylvester.lean) |
| Proposition 3.3 | Finite-shear absorption of external diagonal blocks. | [NoEpsilon.Absorption.identity_corner_absorption](CommutatorTheorem/NoEpsilon/AbsorptionCore.lean) |
| Theorem 4.1 | Finite-support MSS vector selection theorem. | [NoEpsilon.MSSFinite.finite_mss](CommutatorTheorem/NoEpsilon/MSSFinite.lean) |
| Lemma 4.3 | Numerical-range disk in low-codimension compressions. | [NoEpsilon.highMass_compression_contains_disk](CommutatorTheorem/NoEpsilon/HighMassCompression.lean) |
| Lemma 4.4 | Unit vector with zero expectation and large image norm. | [NoEpsilon.exists_unit_neutral_large_image_of_numericalRange](CommutatorTheorem/NoEpsilon/HighMassGeometry.lean) |
| Proposition 4.5 | High-trace-mass branch. | [NoEpsilon.highMass_bounded_commutator](CommutatorTheorem/NoEpsilon/HighMassTheorem.lean) |
| Lemma 4.6 | Simultaneous diagonal control for three Hermitian matrices. | [NoEpsilon.ThreeHermitian.exists_diagonal_control](CommutatorTheorem/NoEpsilon/ThreeHermitianBasis.lean) |
| Lemma 4.7 | Balanced transversals. | [NoEpsilon.LowMassPaving.exists_transversals](CommutatorTheorem/NoEpsilon/LowMassTransversals.lean) |
| Proposition 4.8 | Equal-rank, trace-zero paving. | [NoEpsilon.normalized_low_mass_paving](CommutatorTheorem/NoEpsilon/LowMassTheorem.lean) |
| Lemma 5.1 | Finite block assembly with a common norm budget. | [NoEpsilon.BlockAssembly.assemble_fixed_constants](CommutatorTheorem/NoEpsilon/BlockAssembly.lean) |
| Lemma 5.3 | Recursive skew-matrix identities. | [PavingSeparation.skew_mul_self](PavingSeparation/Family.lean) |
| Lemma 5.4 | Planar inverse-square energy lower bound. | [PavingSeparation.PlanarEnergy.energy_lower_bound](PavingSeparation/PlanarEnergy.lean) |

## Johnson–Ozawa–Schechtman theorem

The separate Epsilon branch formalizes the theorem from Johnson, Ozawa, and Schechtman,
“A quantitative version of the commutator theorem for zero trace matrices,” *Proceedings
of the National Academy of Sciences* (2013), [doi:10.1073/pnas.1202411109](https://doi.org/10.1073/pnas.1202411109).
For every `ε > 0`, a traceless complex `n × n` matrix admits a commutator decomposition
with a normal first factor and a bound of the form `K_ε n^ε ‖A‖`. Its main Lean entry point is
[CommutatorTheorem.main_commutator_theorem_normal](CommutatorTheorem/Epsilon/Main.lean).

## Build and verify

Install Lean's `elan` toolchain manager, then run the following commands from the repository root:

```sh
lake exe cache get
lake build
```

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
