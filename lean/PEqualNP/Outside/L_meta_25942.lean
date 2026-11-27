import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25942
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨.and,[5,2]⟩,⟨.or,[1,8]⟩,⟨.or,[3,6]⟩,⟨.not,[7]⟩,⟨.or,[4,0]⟩,⟨.and,[11,9]⟩,⟨.or,[7,10]⟩,⟨.and,[12,14]⟩,⟨.or,[15,13]⟩], 16⟩

end PEqualNP.Outside.L_meta_25942

theorem PEqualNP.Outside.L_meta_25942 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ i < 4 + 4, g.inputs = [i]) ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([12, 7, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨PEqualNP.Outside.L_meta_25942.C, ?_, by decide, ?_, by decide⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_25942.C] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro g hg
    simp [PEqualNP.Outside.L_meta_25942.C] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
