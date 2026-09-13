import AssertBytes240.Optimality
import AssertBytes240.RecordInstance

/-!
# Public axiom audit

These guarded commands cover the affine component theorem, the
finite-projection theorem, the parametric AssertBytes score theorem, and the
record-gadget instance that shows the hypotheses are satisfiable.
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

/--
info: 'ZkGolfOptimality.RecordInstance.bound_applies' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZkGolfOptimality.RecordInstance.bound_applies
