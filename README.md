# [A Dimension-Independent Commutator Bound](https://arxiv.org/abs/2609.09938)

Lean 4 formalizations of two commutator theorems for traceless complex matrices.
All norms below are Euclidean operator norms, and both factors have the same size as the input.

## Main theorem correspondence
The following lists the Lean entry points corresponding to the paper's results. The main theorem statements agree with the manuscript. Some intermediate results use different formulations or quantitative bounds.

| Paper result | Content | Lean entry point |
|---|---|---|
| Theorem 1.2 | Dimension-independent commutator bound. | [NoEpsilon.uniformCommutatorBound](CommutatorTheorem/NoEpsilon/Main.lean) |
| Theorem 1.4 | Exact paving and normal-factor cost, including the square-normalized λ lower bound. | [PavingSeparation.paving_commutator_separation](PavingSeparation/Theorem1.lean); [PavingSeparation.finFamily_lambdaA_lower_bound](PavingSeparation/Lambda.lean) |
| Lemma 2.1 | Hermitian commutator decomposition with a unitary first factor. | [NoEpsilon.hermitianUnitaryCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean) |
| Corollary 2.2 | Sum of two commutators with unitary first factors. | [NoEpsilon.adaptiveTwoCommutatorBound](CommutatorTheorem/NoEpsilon/CyclicCommutator.lean) |
| Lemma 2.3 | Identity-corner commutator representation. | [NoEpsilon.identityCorner_bounded_from_whole_norm](CommutatorTheorem/NoEpsilon/CoreTheorem.lean) |
| Lemma 2.4 | Rectangular Sylvester equation with separated scalar centers. | [NoEpsilon.exists_sylvester_solution](CommutatorTheorem/NoEpsilon/Sylvester.lean) |
| Proposition 2.6 | Finite-shear absorption of external diagonal blocks. | [NoEpsilon.Absorption.identity_corner_absorption](CommutatorTheorem/NoEpsilon/AbsorptionCore.lean) |
| Theorem 3.1 | MSS vector selection with positive marginal support and positive joint weight. | [NoEpsilon.MSSFinite.finite_mss_supported](CommutatorTheorem/NoEpsilon/MSSFinite.lean); `finite_mss_positive_probability` |
| Lemma 3.4 | Numerical-range disk in low-codimension compressions. | [NoEpsilon.highMass_compression_contains_disk](CommutatorTheorem/NoEpsilon/HighMassCompression.lean) |
| Lemma 3.5 | Unit vector with zero expectation and large image norm. | [NoEpsilon.exists_unit_neutral_large_image_of_numericalRange](CommutatorTheorem/NoEpsilon/HighMassGeometry.lean) |
| Proposition 3.6 | High-trace-mass branch. | [NoEpsilon.highMass_bounded_commutator](CommutatorTheorem/NoEpsilon/HighMassTheorem.lean) |
| Lemma 3.7 | Simultaneous diagonal control for three Hermitian matrices. | [NoEpsilon.ThreeHermitian.exists_diagonal_control](CommutatorTheorem/NoEpsilon/ThreeHermitianBasis.lean) |
| Lemma 3.8 | Balanced transversals. | [NoEpsilon.LowMassPaving.exists_transversals](CommutatorTheorem/NoEpsilon/LowMassTransversals.lean) |
| Proposition 3.9 | Equal-rank, trace-zero paving. | [NoEpsilon.normalized_low_mass_paving](CommutatorTheorem/NoEpsilon/LowMassTheorem.lean) |
| Lemma 3.11 | Finite block assembly with a common norm budget. | [NoEpsilon.BlockAssembly.assemble_fixed_constants](CommutatorTheorem/NoEpsilon/BlockAssembly.lean) |
| Lemma 4.1 | Recursive skew-matrix identities. | [PavingSeparation.skew_mul_self](PavingSeparation/Family.lean) |
| Lemma 4.2 | Planar inverse-square energy lower bound. | [PavingSeparation.PlanarEnergy.energy_lower_bound](PavingSeparation/PlanarEnergy.lean) |

## Formal statement alignment for the revised manuscript

The numbering in the table above follows
[A Dimension-Independent Commutator Bound](https://arxiv.org/abs/2609.09938).
The following public declarations clarify the MSS and Kadison–Singer formulations:

- `NoEpsilon.MSSFinite.finite_mss_supported` retains the hypotheses of `finite_mss`
  and concludes that the selected outcome satisfies `∀ i, 0 < p i (q i)`, together
  with the same Euclidean operator norm bound. Zero-weight vector values are replaced
  by values from positive support before applying `finite_mss`; all weighted
  covariances and expected energies are unchanged. The corollary
  `finite_mss_positive_probability` gives `0 < ∏ i, p i (q i)`, the probability of
  that outcome under the finite independent product law. The original `finite_mss`
  remains available. In the paired selection used by Lemma 3.8, all four outcomes
  already have weight `1 / 4` (`MSSPaired.lean`).
- [`KadisonSinger.kadison_singer_state_extension`](KadisonSinger/Main.lean)
  states `∃! ψ : State Operator, ∀ d : Diagonal,
  ψ.val (diagonalRepresentation d) = φ.val d`, assuming only that `φ` is pure.
  Uniqueness ranges over **all states**, with no purity condition on `ψ`.
  The existing `kadison_singer` follows by proving that this unique extension is
  pure; its uniqueness quantifier alone ranges over pure extensions. Appendix A
  correctly displays `kadison_singer` and explains the stronger all-state extension result.

The commands below check the declarations and their axiom dependencies.
Appendix A uses the `Matrix.Norms.L2Operator` norm convention and retains the definitions of `lp`, `Matrix.vecMulVec`,
and `Matrix.diagonal`. State positivity, normalization, purity,
and the faithful diagonal representation are described in
[`KadisonSinger/README.md`](KadisonSinger/README.md).

```sh
lake build
lake env lean PaperCorrespondence.lean
lake env lean KadisonSinger/Verification.lean
```

The two audit files print the supported MSS statements and the all-state
Kadison–Singer statement, and check their transitive axiom dependencies.
Expected axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

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
