import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21294

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [12, 17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40446 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_21294

theorem PEqualNP.Outside.L_meta_21294 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40446 : ℕ).testBit (5 * u.val + v.val)) 11) :=
  PEqualNP.Outside.L_meta_21294.main_aux
