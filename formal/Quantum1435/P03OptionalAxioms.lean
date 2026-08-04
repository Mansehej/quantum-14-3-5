import Quantum1435.P03ThresholdBounds

/-!
Run this file only after building the opt-in p03 normal-form checks:

`lake env lean Quantum1435/P03OptionalAxioms.lean`

These checks provide an independent exact-coordinate cross-check. The final
nonexistence theorem uses representative-free invariant bounds instead and
does not depend on any declaration audited here.
-/

#print axioms Quantum1435.rankThree_sparse_degree_le_one
#print axioms Quantum1435.rankTwo0_sparse_degree_le_one
#print axioms Quantum1435.rankTwo1_sparse_high_iff
#print axioms Quantum1435.rankTwo2_sparse_high_iff
#print axioms Quantum1435.p03CollisionScore_eq_sparse
#print axioms Quantum1435.rankTwo1_selected_exception_card_le_one
#print axioms Quantum1435.rankTwo2_selected_exception_card_le_eight
#print axioms Quantum1435.rankThree_selected_sum_le_24
#print axioms Quantum1435.rankTwo0_selected_sum_le_24
#print axioms Quantum1435.rankTwo1_selected_sum_le_26
#print axioms Quantum1435.rankTwo2_selected_sum_le_56
#print axioms Quantum1435.p03_checked_collision_contradiction
