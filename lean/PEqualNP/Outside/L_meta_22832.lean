import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22832

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 0]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.or, [10, 1]⟩,
        ⟨GateOp.or, [6, 9]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [8, 14]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [11, 16]⟩,
        ⟨GateOp.and, [13, 18]⟩,
        ⟨GateOp.or, [17, 15]⟩,
        ⟨GateOp.and, [12, 20]⟩,
        ⟨GateOp.or, [21, 19]⟩ ],
    output := 22 }

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843262 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22832

theorem PEqualNP.Outside.L_meta_22832 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843262 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  exact ⟨PEqualNP.Outside.L_meta_22832.circ, PEqualNP.Outside.L_meta_22832.circ_mono, by decide, PEqualNP.Outside.L_meta_22832.circ_rep⟩
