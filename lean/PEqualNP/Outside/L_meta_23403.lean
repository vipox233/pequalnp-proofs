import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23403

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [8, 11]⟩], 12⟩

theorem witness_fanInTwo : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_rows : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (233019 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_23403

theorem PEqualNP.Outside.L_meta_23403 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (233019 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23403.witness, PEqualNP.Outside.L_meta_23403.witness_fanInTwo, by decide, PEqualNP.Outside.L_meta_23403.witness_rows⟩
