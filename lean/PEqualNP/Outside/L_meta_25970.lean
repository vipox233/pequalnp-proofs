import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25970

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [13]⟩], output := 14 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25970

theorem PEqualNP.Outside.L_meta_25970 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([13, 11, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_25970.c1, PEqualNP.Outside.L_meta_25970.f1, by decide +kernel, by decide +kernel, by decide +kernel⟩
