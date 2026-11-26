import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20539_aux

open PEqualNP.CircuitLowerBounds

-- The output adds the full first column to the values on columns one through four.
def witness : Circuit :=
  { gates := [
      ⟨.or, [2, 7]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.or, [6, 8]⟩,
      ⟨.or, [9, 10]⟩,
      ⟨.and, [9, 10]⟩,
      ⟨.or, [1, 5]⟩,
      ⟨.or, [12, 13]⟩,
      ⟨.and, [11, 14]⟩,
      ⟨.or, [3, 15]⟩]
    output := 16 }

end PEqualNP.Outside.L_meta_20539_aux

theorem PEqualNP.Outside.L_meta_20539 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 3) (v : Fin 5) => (8061 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  open PEqualNP.Outside.L_meta_20539_aux in
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
