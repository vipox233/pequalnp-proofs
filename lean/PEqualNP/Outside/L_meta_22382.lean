import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22382_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [19, 20]⟩], 21⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843006 : ℕ).testBit (6 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22382_aux

theorem PEqualNP.Outside.L_meta_22382 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843006 : ℕ).testBit (6 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_22382_aux.rep
