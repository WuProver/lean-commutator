import KadisonSinger

/-!
# Public theorem signatures and axiom audit

Run `lake env lean KadisonSinger/Verification.lean` after `lake build`.
Every reported axiom closure should be contained in
`[propext, Classical.choice, Quot.sound]`.
-/

#check KadisonSinger.kadison_singer
#check KadisonSinger.kadison_singer_state_extension
#check NoEpsilon.MSSFinite.finite_mss_supported
#check NoEpsilon.MSSFinite.finite_mss_positive_probability
#check KadisonSinger.hermitian_paving
#check KadisonSinger.selfAdjoint_operator_paving
#check KadisonSinger.mem_range_diagonalRepresentation_iff
#check KadisonSinger.State.isPure_iff_extreme

#print axioms NoEpsilon.MSSFinite.finite_mss
#print axioms NoEpsilon.MSSFinite.finite_mss_supported
#print axioms NoEpsilon.MSSFinite.finite_mss_positive_probability
#print axioms KadisonSinger.vector_partition
#print axioms KadisonSinger.vector_partition_le
#print axioms KadisonSinger.weaver_ks2
#print axioms KadisonSinger.hermitian_paving
#print axioms KadisonSinger.hermitian_kernel_paving
#print axioms KadisonSinger.finiteSection_norm_le
#print axioms KadisonSinger.norm_le_of_finiteSection
#print axioms KadisonSinger.selfAdjoint_operator_paving
#print axioms KadisonSinger.diagonalExpectation
#print axioms KadisonSinger.diagonalExpectation_one
#print axioms KadisonSinger.diagonalExpectation_representation
#print axioms KadisonSinger.diagonalRepresentation_isometry
#print axioms KadisonSinger.mem_range_diagonalRepresentation_iff
#print axioms KadisonSinger.State.isPure_iff_extreme
#print axioms KadisonSinger.diagonal_selfAdjoint_paving
#print axioms KadisonSinger.kadison_singer_state_extension
#print axioms KadisonSinger.kadison_singer
