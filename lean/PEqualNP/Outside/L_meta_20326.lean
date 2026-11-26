import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20326
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def net : Circuit := ⟨[⟨.or,[0,11]⟩, ⟨.or,[5,9]⟩, ⟨.or,[7,13]⟩, ⟨.or,[4,10]⟩, ⟨.or,[2,15]⟩, ⟨.or,[16,20]⟩, ⟨.or,[19,21]⟩, ⟨.or,[6,14]⟩, ⟨.or,[17,23]⟩, ⟨.or,[18,24]⟩, ⟨.or,[1,2]⟩, ⟨.or,[12,26]⟩, ⟨.or,[14,27]⟩, ⟨.or,[3,6]⟩, ⟨.or,[8,29]⟩, ⟨.or,[15,30]⟩, ⟨.or,[3,12]⟩, ⟨.or,[16,32]⟩, ⟨.or,[17,33]⟩, ⟨.or,[1,8]⟩, ⟨.or,[18,35]⟩, ⟨.or,[19,36]⟩, ⟨.and,[34,37]⟩, ⟨.and,[22,25]⟩, ⟨.and,[28,31]⟩, ⟨.or,[38,39]⟩, ⟨.or,[40,41]⟩],42⟩

theorem basis : Monotone2 net := by
  intro g hg
  simp only [net,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst g <;> simp

theorem sem : Represents (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) net := by
  change ∀ u v : Fin 8, net.eval (oneEach u v) = _
  decide +kernel

end PEqualNP.Outside.L_meta_20326

theorem PEqualNP.Outside.L_meta_20326 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  open PEqualNP.Outside.L_meta_20326 in
  exact ⟨net,basis,by decide,sem⟩
