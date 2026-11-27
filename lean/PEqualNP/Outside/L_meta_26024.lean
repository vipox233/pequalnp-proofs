import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26024

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [3, 7]⟩, ⟨GateOp.not, [8]⟩], 9⟩

theorem witness_fanInTwo : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

theorem witness_notCount : PEqualNP.NotBracket.notCount witness ≤ 1 := by
  decide

theorem witness_represents : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 4) => (([15, 15, 15, 7] : List ℕ).getD u.val 0).testBit v.val) witness := by
  decide

end PEqualNP.Outside.L_meta_26024

theorem PEqualNP.Outside.L_meta_26024 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 15, 15, 7] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_26024.witness, PEqualNP.Outside.L_meta_26024.witness_fanInTwo, by decide,
    PEqualNP.Outside.L_meta_26024.witness_notCount, PEqualNP.Outside.L_meta_26024.witness_represents⟩
