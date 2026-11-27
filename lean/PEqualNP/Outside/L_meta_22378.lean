import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22378_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 4]⟩], 22⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841719 : ℕ).testBit (6 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22378_aux

theorem PEqualNP.Outside.L_meta_22378 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841719 : ℕ).testBit (6 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_22378_aux.rep
