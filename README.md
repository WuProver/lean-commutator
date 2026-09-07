# A dimension-independent commutator bound via trace-mass splitting

Lean 4 formalization of the dimension-independent commutator bound and the accompanying paving separation results.

The main theorem states that there is a constant $K > 0$, independent of dimension, such that every traceless complex matrix $A$ admits matrices $B,C$ of the same size satisfying

$$
A = BC - CB, \qquad \|B\|\,\|C\| \le K\|A\|.
$$

All norms are Euclidean operator norms. The factors are not required to be normal.

## Paper–code correspondence

The numbering below follows the September 5, 2026 paper, as indexed in [README_CN.md](README_CN.md). See that document for detailed statement comparisons, definitions, constants, and auxiliary results. Names in `PavingSeparation` retain their original numbering.

| Paper result | Content | Lean entry points |
|---|---|---|
| Theorem 1.1 | Dimension-independent commutator bound. | [NoEpsilon.uniformCommutatorBound](CommutatorTheorem/NoEpsilon/Main.lean) |
| Theorem 1.4 | Exact paving and normal-factor cost; use the second entry for the square-normalized λ lower bound. | [PavingSeparation.theorem1](PavingSeparation/Theorem1.lean); [PavingSeparation.finFamily_lambdaA_lower_bound](PavingSeparation/Lambda.lean) |
| Lemma 2.1 | Hermitian commutator decomposition with a unitary first factor. | [NoEpsilon.hermitianUnitaryCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean) |
| Corollary 2.2 | Sum of two commutators with unitary first factors. | [NoEpsilon.adaptiveTwoCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean) |
| Lemma 3.1 | Bounded commutator representation of the identity-corner core. | [NoEpsilon.identityCorner_bounded_from_whole_norm](CommutatorTheorem/NoEpsilon/CoreTheorem.lean) |
| Lemma 3.2 | Rectangular Sylvester equation with separated scalar centers. | [NoEpsilon.exists_sylvester_solution](CommutatorTheorem/NoEpsilon/Sylvester.lean) |
| Proposition 3.3 | Finite-shear absorption of external diagonal blocks. | [NoEpsilon.Absorption.identity_corner_absorption](CommutatorTheorem/NoEpsilon/AbsorptionCore.lean) |
| Theorem 4.1 | Finite-support MSS vector selection theorem. | [NoEpsilon.MSSFinite.finite_mss](CommutatorTheorem/NoEpsilon/MSSFinite.lean) |
| Lemma 4.3 | Numerical-range disk in low-codimension compressions. | [NoEpsilon.highMass_compression_contains_disk](CommutatorTheorem/NoEpsilon/HighMassCompression.lean) |
| Lemma 4.4 | Unit vector with zero expectation and large image norm. | [NoEpsilon.exists_unit_neutral_large_image_of_numericalRange](CommutatorTheorem/NoEpsilon/HighMassGeometry.lean) |
| Proposition 4.5 | High-trace-mass branch (normalized formulation). | [NoEpsilon.highMass_bounded_commutator](CommutatorTheorem/NoEpsilon/HighMassTheorem.lean) |
| Lemma 4.6 | Simultaneous diagonal control for three Hermitian matrices. | [NoEpsilon.ThreeHermitian.exists_diagonal_control](CommutatorTheorem/NoEpsilon/ThreeHermitianBasis.lean) |
| Lemma 4.7 | Balanced transversals; combined with the proved `pairedHalfSelection` input. | [NoEpsilon.LowMassPaving.exists_transversals](CommutatorTheorem/NoEpsilon/LowMassTransversals.lean) |
| Proposition 4.8 | Equal-rank, trace-zero paving; the final interface uses `¬ HasHighTraceMass`. | [NoEpsilon.normalized_low_mass_paving](CommutatorTheorem/NoEpsilon/LowMassTheorem.lean) |
| Lemma 5.1 | Finite block assembly with a common norm budget. | [NoEpsilon.BlockAssembly.assemble_fixed_constants](CommutatorTheorem/NoEpsilon/BlockAssembly.lean) |
| Lemma 5.3 | Recursive skew-matrix identities (combined statements). | [PavingSeparation.skew_mul_self](PavingSeparation/Family.lean); [PavingSeparation.skew_offdiag_eq_one_or_neg_one](PavingSeparation/Family.lean) |
| Lemma 5.4 | Planar inverse-square energy lower bound. | [PavingSeparation.PlanarEnergy.energy_lower_bound](PavingSeparation/PlanarEnergy.lean) |

Some rows combine several declarations or use normalized formulations. In particular, Proposition 4.8's non-strict boundary condition requires lower-level interfaces, and the paper's full μ specification is not covered by this table.

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

These checks resolve the indexed declarations and print the axioms of key results. The expected axioms are `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`. For a broader audit:

```sh
lake env lean CommutatorTheorem/NoEpsilon/AxiomAudit.lean
```

## License

Copyright (c) 2026 lean-commutator contributors.

This project's Lean source code is licensed under the [Apache License 2.0](LICENSE). Dependencies retain their own licenses.
