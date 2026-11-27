import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22676

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.and, [1, 17]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [2, 20]⟩, ⟨GateOp.and, [19, 21]⟩, ⟨GateOp.or, [18, 22]⟩], 23⟩

theorem witness_mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_represents : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (841724 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide

end PEqualNP.Outside.L_meta_22676

theorem PEqualNP.Outside.L_meta_22676 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841724 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨PEqualNP.Outside.L_meta_22676.witness, PEqualNP.Outside.L_meta_22676.witness_mono, by decide, PEqualNP.Outside.L_meta_22676.witness_represents⟩
