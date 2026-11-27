import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26011
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨.and,[1,5]⟩,⟨.or,[4,0]⟩,⟨.or,[1,5]⟩,⟨.or,[9,10]⟩,⟨.not,[8]⟩,⟨.and,[11,12]⟩], 13⟩

end PEqualNP.Outside.L_meta_26011

theorem PEqualNP.Outside.L_meta_26011 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 3, 3] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨PEqualNP.Outside.L_meta_26011.C, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp [PEqualNP.Outside.L_meta_26011.C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
