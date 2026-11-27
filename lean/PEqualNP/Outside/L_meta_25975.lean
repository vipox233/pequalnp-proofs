import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25975

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 6, 1, 1] : List ℕ).getD u.val 0).testBit v.val) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 6, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide, witness_ok⟩

end PEqualNP.Outside.L_meta_25975

theorem PEqualNP.Outside.L_meta_25975 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 6, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  PEqualNP.Outside.L_meta_25975.solve
