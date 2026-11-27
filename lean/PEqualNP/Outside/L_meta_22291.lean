import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22291
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or,[0,6]⟩, ⟨.or,[1,7]⟩, ⟨.or,[2,8]⟩,
    ⟨.or,[11,9]⟩, ⟨.and,[10,13]⟩, ⟨.or,[10,11]⟩,
    ⟨.and,[15,12]⟩, ⟨.or,[14,16]⟩, ⟨.or,[4,5]⟩,
    ⟨.or,[0,1]⟩, ⟨.or,[19,3]⟩, ⟨.and,[18,20]⟩,
    ⟨.or,[17,21]⟩],22⟩

theorem monotone : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22291

theorem PEqualNP.Outside.L_meta_22291 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837115 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22291.witness,PEqualNP.Outside.L_meta_22291.monotone,by decide,by decide +kernel⟩
