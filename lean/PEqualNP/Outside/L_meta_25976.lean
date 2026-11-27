import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25976

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [4, 10]⟩, ⟨.not, [12]⟩, ⟨.or, [11, 13]⟩], 14⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 6, 1, 1] : List ℕ).getD u.val 0).testBit v.val) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 6, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide, witness_ok⟩

end PEqualNP.Outside.L_meta_25976

theorem PEqualNP.Outside.L_meta_25976 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 6, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  PEqualNP.Outside.L_meta_25976.solve
