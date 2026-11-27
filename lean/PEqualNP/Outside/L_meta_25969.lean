import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25969

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩], output := 11 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25969

theorem PEqualNP.Outside.L_meta_25969 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 7, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_25969.c1, PEqualNP.Outside.L_meta_25969.f1, by decide +kernel, by decide +kernel, by decide +kernel⟩
