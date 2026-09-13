import AssertBytes240.Optimality

/-!
# Public axiom audit

These guarded commands cover the affine component theorem, the
finite-projection theorem, and the parametric AssertBytes score theorem.
-/

/--
info: 'ZkGolfOptimality.AffineBezout.minimalPrimes_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZkGolfOptimality.AffineBezout.minimalPrimes_ncard_le

/--
info: 'ZkGolfOptimality.AffineBezout.scalar_projection_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZkGolfOptimality.AffineBezout.scalar_projection_ncard_le

/--
info: 'ZkGolfOptimality.AssertBytes.score_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZkGolfOptimality.AssertBytes.score_lower_bound
