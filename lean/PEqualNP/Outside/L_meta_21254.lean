import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21254

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [4, 0]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [11, 9]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [10, 1]⟩,
        ⟨GateOp.or, [5, 13]⟩,
        ⟨GateOp.or, [5, 10]⟩,
        ⟨GateOp.and, [16, 12]⟩,
        ⟨GateOp.and, [14, 15]⟩,
        ⟨GateOp.or, [17, 18]⟩ ],
    output := 19 }

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (36094 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_21254

theorem PEqualNP.Outside.L_meta_21254 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36094 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21254.circ, PEqualNP.Outside.L_meta_21254.circ_mono, by decide, PEqualNP.Outside.L_meta_21254.circ_rep⟩
