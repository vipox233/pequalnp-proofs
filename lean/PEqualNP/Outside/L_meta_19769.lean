import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19769
def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[9,12]⟩,⟨.or,[11,13]⟩,⟨.or,[14,15]⟩,⟨.or,[8,17]⟩,⟨.and,[0,19]⟩,⟨.or,[8,12]⟩,⟨.or,[21,14]⟩,⟨.and,[1,22]⟩,⟨.or,[10,16]⟩,⟨.and,[2,24]⟩,⟨.or,[10,17]⟩,⟨.and,[3,26]⟩,⟨.or,[13,18]⟩,⟨.and,[4,28]⟩,⟨.or,[10,18]⟩,⟨.and,[5,30]⟩,⟨.or,[8,9]⟩,⟨.or,[32,15]⟩,⟨.and,[6,33]⟩,⟨.or,[11,16]⟩,⟨.and,[7,35]⟩,⟨.or,[20,23]⟩,⟨.or,[37,25]⟩,⟨.or,[38,27]⟩,⟨.or,[39,29]⟩,⟨.or,[40,31]⟩,⟨.or,[41,34]⟩,⟨.or,[42,36]⟩],43⟩
end PEqualNP.Outside.L_meta_19769
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19769 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1910587134026600745 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨PEqualNP.Outside.L_meta_19769.circuit, by simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_19769.circuit], by decide +kernel, by decide +kernel⟩
