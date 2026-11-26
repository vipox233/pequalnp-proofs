import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19706_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [15]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [14, 18]⟩], 19⟩

theorem fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19706_aux

theorem PEqualNP.Outside.L_meta_19706 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16254161 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19706_aux.circuit, PEqualNP.Outside.L_meta_19706_aux.fan, by decide, by decide +kernel⟩
