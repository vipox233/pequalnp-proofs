import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26018

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 13, 3] : List ℕ).getD u.val 0).testBit v.val) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 13, 3] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide, witness_ok⟩

end PEqualNP.Outside.L_meta_26018

theorem PEqualNP.Outside.L_meta_26018 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 13, 3] : List ℕ).getD u.val 0).testBit v.val) C :=
  PEqualNP.Outside.L_meta_26018.solve
