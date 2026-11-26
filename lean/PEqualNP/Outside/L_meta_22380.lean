import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22380_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 16]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [21, 20]⟩], 22⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 13 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rep : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (842996 : ℕ).testBit (6 * u.val + v.val)) 13) := ⟨witness, mono, small, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22380_aux

theorem PEqualNP.Outside.L_meta_22380 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (842996 : ℕ).testBit (6 * u.val + v.val)) 13) := PEqualNP.Outside.L_meta_22380_aux.rep
