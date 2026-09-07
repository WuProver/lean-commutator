import CommutatorTheorem.NoEpsilon.Goal
import CommutatorTheorem.NoEpsilon.Main
import CommutatorTheorem.NoEpsilon.BlockAlgebra
import CommutatorTheorem.NoEpsilon.Shear
import CommutatorTheorem.NoEpsilon.Riccati
import CommutatorTheorem.NoEpsilon.IdentityCorner
import CommutatorTheorem.NoEpsilon.NormBounds
import CommutatorTheorem.NoEpsilon.CyclicCommutator
import CommutatorTheorem.NoEpsilon.CoreTheorem
import CommutatorTheorem.NoEpsilon.Sylvester
import CommutatorTheorem.NoEpsilon.BlockAssembly
import CommutatorTheorem.NoEpsilon.MSSSelection
import CommutatorTheorem.NoEpsilon.HighMassGeometry
import CommutatorTheorem.NoEpsilon.HighMassCompression
import CommutatorTheorem.NoEpsilon.Steinitz
import CommutatorTheorem.NoEpsilon.MixedCharacteristic
import CommutatorTheorem.NoEpsilon.MSSStability
import CommutatorTheorem.NoEpsilon.FiniteAbsorption
import CommutatorTheorem.NoEpsilon.AbsorptionCore
import CommutatorTheorem.NoEpsilon.DiagonalAbsorption
import CommutatorTheorem.NoEpsilon.FinitePartition
import CommutatorTheorem.NoEpsilon.HighMassTheorem
import CommutatorTheorem.NoEpsilon.SteinitzGrouping
import CommutatorTheorem.NoEpsilon.MSSBarrier
import CommutatorTheorem.NoEpsilon.ThreeHermitianBasis
import CommutatorTheorem.NoEpsilon.MSSPartialFractions
import CommutatorTheorem.NoEpsilon.Induction

/-!
# The no-epsilon theorem and its verified components

The main theorem is `NoEpsilon.uniformCommutatorBound`, proving the exact target
`NoEpsilon.UniformCommutatorBound`. Its full kernel dependency audit is in the repository-root `AxiomAudit.lean`.
-/
