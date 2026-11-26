import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20801

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, witness_ok⟩


end PEqualNP.Outside.L_meta_20801

theorem PEqualNP.Outside.L_meta_20801 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_20801.solve
