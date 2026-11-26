import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21356

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [6, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [11, 12]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [10, 17]⟩,
    ⟨.or, [4, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_21356

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_21356 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241141 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_21356.witness, ?_, by decide +kernel, by decide +kernel⟩
  exact by simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21356.witness, List.mem_cons, List.not_mem_nil]
