import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [7, 13]⟩, ⟨.not, [14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, witness_ok⟩


end PEqualNP.Outside.L_meta_19600

theorem PEqualNP.Outside.L_meta_19600 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19600.solve
