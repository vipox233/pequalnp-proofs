import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20849

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [10, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [4, 15]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [17, 14]⟩, ⟨GateOp.or, [18, 16]⟩], 19⟩

theorem wit_mono : Monotone2 wit := by
  simp [wit, Monotone2]

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25364513 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20849

theorem PEqualNP.Outside.L_meta_20849 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25364513 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_20849.main_aux
