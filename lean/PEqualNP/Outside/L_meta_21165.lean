import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21165

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

private def witness : Circuit := ⟨[⟨.or,[0,4]⟩,⟨.or,[5,3]⟩,⟨.or,[10,6]⟩,
  ⟨.or,[1,0]⟩,⟨.or,[2,9]⟩,⟨.or,[11,7]⟩,⟨.or,[8,11]⟩,⟨.and,[14,13]⟩,
  ⟨.and,[12,15]⟩,⟨.or,[17,16]⟩],18⟩

private theorem monotone : Monotone2 witness := by
  have strict : IsAO2 9 witness := by decide +kernel
  intro g hg
  exact ⟨by simpa using strict.1 g hg,(strict.2.2 g hg).le⟩

end PEqualNP.Outside.L_meta_21165

theorem PEqualNP.Outside.L_meta_21165 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47838 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨L_meta_21165.witness,L_meta_21165.monotone,by decide,by decide +kernel⟩