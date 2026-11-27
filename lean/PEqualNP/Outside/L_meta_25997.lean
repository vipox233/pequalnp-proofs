import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25997

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [4, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [11, 15]⟩], 16⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 11, 6, 1] : List ℕ).getD u.val 0).testBit v.val) witness := by
  decide +kernel

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 11, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide, witness_ok⟩

end PEqualNP.Outside.L_meta_25997

theorem PEqualNP.Outside.L_meta_25997 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 11, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  PEqualNP.Outside.L_meta_25997.solve
