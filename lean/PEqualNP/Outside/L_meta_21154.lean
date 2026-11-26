import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21154

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [0, 1]⟩,
    ⟨.or, [7, 8]⟩, ⟨.or, [5, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [10, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_21154

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_21154 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39771 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨PEqualNP.Outside.L_meta_21154.witness, ?_, by decide +kernel, by decide +kernel⟩
  exact by simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21154.witness, List.mem_cons, List.not_mem_nil]
