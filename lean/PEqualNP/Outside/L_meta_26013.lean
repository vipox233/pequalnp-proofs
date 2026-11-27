import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26013
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨.or,[4,2]⟩,⟨.or,[0,8]⟩,⟨.or,[5,1]⟩,⟨.or,[10,7]⟩,⟨.and,[8,11]⟩,⟨.not,[12]⟩,⟨.or,[9,10]⟩,⟨.and,[14,13]⟩], 15⟩

end PEqualNP.Outside.L_meta_26013

theorem PEqualNP.Outside.L_meta_26013 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 5, 3] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨PEqualNP.Outside.L_meta_26013.C, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp [PEqualNP.Outside.L_meta_26013.C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
