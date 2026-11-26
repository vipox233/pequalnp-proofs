import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21167_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [17, 16]⟩], 18⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 10 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47871 : ℕ).testBit (5 * u.val + v.val)) 10) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21167_aux

theorem PEqualNP.Outside.L_meta_21167 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47871 : ℕ).testBit (5 * u.val + v.val)) 10) := PEqualNP.Outside.L_meta_21167_aux.rep
