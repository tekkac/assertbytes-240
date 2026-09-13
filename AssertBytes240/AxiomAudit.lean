import AssertBytes240.Optimality
import AssertBytes240.RecordInstance
import AssertBytes240.RecordInstance16

/-!
# Public axiom audit

These guarded commands cover the affine component theorem, the
finite-projection theorem, the parametric AssertBytes score theorem, and the
one-byte and sixteen-byte record instances.
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

/--
info: 'ZkGolfOptimality.RecordInstance16.bound_applies16' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZkGolfOptimality.RecordInstance16.bound_applies16

/--
info: 'ZkGolfOptimality.RecordInstance16.checksBytes16_of_charP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZkGolfOptimality.RecordInstance16.checksBytes16_of_charP
