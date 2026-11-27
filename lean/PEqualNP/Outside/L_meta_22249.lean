import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22249

def upperA : Fin 4 → Fin 6 → Bool :=
  fun (u : Fin 4) (v : Fin 6) => (815994 : ℕ).testBit (6 * u.val + v.val)

def upperC : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [1, 5]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 17]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [18, 16]⟩, ⟨.or, [19, 20]⟩], 21⟩

theorem upper_mono : PEqualNP.MetaComplexity.Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents upperA upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_22249

theorem PEqualNP.Outside.L_meta_22249 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815994 : ℕ).testBit (6 * u.val + v.val)) 13) :=
  ⟨PEqualNP.Outside.L_meta_22249.upperC, PEqualNP.Outside.L_meta_22249.upper_mono, by decide, PEqualNP.Outside.L_meta_22249.upper_rep⟩
