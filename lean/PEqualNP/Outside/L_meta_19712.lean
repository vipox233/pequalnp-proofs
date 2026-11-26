import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19712

def witness : Circuit := ⟨[
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [10, 16]⟩,
    ⟨GateOp.and, [0, 19]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [21, 13]⟩,
    ⟨GateOp.and, [1, 22]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.and, [2, 24]⟩,
    ⟨GateOp.or, [12, 18]⟩,
    ⟨GateOp.and, [3, 26]⟩,
    ⟨GateOp.or, [9, 17]⟩,
    ⟨GateOp.and, [4, 28]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [30, 14]⟩,
    ⟨GateOp.and, [5, 31]⟩,
    ⟨GateOp.or, [8, 17]⟩,
    ⟨GateOp.and, [6, 33]⟩,
    ⟨GateOp.or, [9, 18]⟩,
    ⟨GateOp.and, [7, 35]⟩,
    ⟨GateOp.or, [20, 23]⟩,
    ⟨GateOp.or, [37, 25]⟩,
    ⟨GateOp.or, [38, 27]⟩,
    ⟨GateOp.or, [39, 29]⟩,
    ⟨GateOp.or, [40, 32]⟩,
    ⟨GateOp.or, [41, 34]⟩,
    ⟨GateOp.or, [42, 36]⟩
  ], 43⟩

lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19712

theorem PEqualNP.Outside.L_meta_19712 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (838035264769107540 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨PEqualNP.Outside.L_meta_19712.witness, PEqualNP.Outside.L_meta_19712.witness_mono, by decide, by decide +kernel⟩
