# Kadison–Singer from finite MSS selection

This development proves the original Kadison–Singer pure-state extension theorem,
starting from `NoEpsilon.MSSFinite.finite_mss` in the existing project.

The entry point matching uniqueness among **all** state extensions is
`KadisonSinger.kadison_singer_state_extension` in `Main.lean`: every pure state
on the algebra of bounded diagonal operators on ℓ²(ℕ) has a unique state extension
to all bounded operators on ℓ²(ℕ). There is no purity assumption on the extension
in this uniqueness statement. Display this theorem when stating all-state uniqueness.
`KadisonSinger.kadison_singer` is its pure-extension corollary: the unique state
extension is itself pure, as proved in `PureExtension.lean`.
Neither endpoint assumes paving or the existence of an extension.

For the positive-probability MSS formulation, the public corollaries
`NoEpsilon.MSSFinite.finite_mss_supported` and `finite_mss_positive_probability`
provide positive marginal support and positive joint weight, respectively.
The internal use of `finite_mss` remains compatible with these stronger statements.

The concrete spaces are `Hilbert = lp (fun _ : ℕ ↦ ℂ) 2`,
`Operator = Hilbert →L[ℂ] Hilbert`, and `Diagonal = lp (fun _ : ℕ ↦ ℂ) ∞`.
States are positive complex-linear functionals taking the identity to one;
purity is the ordinary extreme-point condition. The diagonal representation is
proved faithful and isometric, with range exactly the coordinate-diagonal operators.
Finite matrix norms are Euclidean operator norms.

The proof follows these steps:

1. `VectorPartition.lean`: MSS Corollary 1.5, including covariance bounded above by the identity.
2. `FinitePaving.lean`: dimension-independent paving for Hermitian zero-diagonal matrices.
3. `Infinite.lean`, `FiniteCompression.lean`, `OperatorPaving.lean`: Rado compactness and
   finite-coordinate density give paving on B(ℓ²(ℕ)).
4. `DiagonalOperators.lean`, `DiagonalExpectation.lean`: the actual diagonal algebra and
   its positive unital expectation.
5. `States.lean`, `PureExtension.lean`, `Main.lean`: paving gives unique state extension;
   purity of the restriction implies purity of that extension.

`Weaver.lean` also proves Weaver's KS₂ in covariance form with η = 18 and θ = 2.

## Build and verify

From the repository root:

```sh
lake build
lake env lean KadisonSinger/Verification.lean
```

Use `lake build KadisonSinger` to build only this library and its dependencies.
The project pins Lean 4.30.0-rc1 and mathlib commit
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`.
`Verification.lean` audits 20 declarations, including both final theorems and
the two supported-selection MSS corollaries. Re-run the commands above for the
current checkout; every axiom closure should contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or additional axioms.
The files `verification/axioms.txt`, `verification/build.log`, and
`verification/summary.json` record an earlier audit and its source fingerprints;
they are not refreshed by the commands above.

## Reference

A. W. Marcus, D. A. Spielman, and N. Srivastava,
*Interlacing families II: Mixed characteristic polynomials and the Kadison–Singer problem*,
Annals of Mathematics **182** (2015), 327–350.
[Published article](https://doi.org/10.4007/annals.2015.182.1.8).
The development uses Corollary 1.5, the finite paving conclusion of Section 6,
and the original pure-state formulation in Question 1.1. The finite paving proof
uses the positive contractions (I ± T)/2 in place of an explicit projection dilation.
