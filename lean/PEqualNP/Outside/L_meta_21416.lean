import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21416

def circuit21416 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
   ⟨.or, [6, 7]⟩,
   ⟨.and, [9, 10]⟩,
   ⟨.or, [4, 5]⟩,
   ⟨.or, [1, 3]⟩,
   ⟨.and, [12, 13]⟩,
   ⟨.or, [0, 1]⟩,
   ⟨.or, [6, 8]⟩,
   ⟨.or, [4, 16]⟩,
   ⟨.and, [15, 17]⟩,
   ⟨.or, [14, 18]⟩,
   ⟨.or, [11, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_21416

open PEqualNP.Outside.L_meta_21416

theorem PEqualNP.Outside.L_meta_21416 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (111357 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨circuit21416, ?_, by decide +kernel, by decide +kernel⟩
  intro gate hg
  simp only [circuit21416, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
