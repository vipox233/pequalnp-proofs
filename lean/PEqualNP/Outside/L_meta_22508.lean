import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22508

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.or, [8, 7]⟩,
        ⟨GateOp.or, [3, 10]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.and, [7, 10]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.or, [11, 15]⟩,
        ⟨GateOp.or, [15, 6]⟩,
        ⟨GateOp.or, [12, 11]⟩,
        ⟨GateOp.or, [14, 1]⟩,
        ⟨GateOp.and, [16, 19]⟩,
        ⟨GateOp.and, [18, 17]⟩,
        ⟨GateOp.or, [21, 20]⟩ ],
    output := 22 }

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1898232 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_22508

theorem PEqualNP.Outside.L_meta_22508 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898232 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22508.circ, PEqualNP.Outside.L_meta_22508.circ_mono, by decide, PEqualNP.Outside.L_meta_22508.circ_rep⟩
