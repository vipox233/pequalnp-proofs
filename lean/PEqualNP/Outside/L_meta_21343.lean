import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21343_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.and, [5, 15]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [17, 18]⟩], 19⟩

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

theorem C_size : C.size ≤ 11 := by decide

theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (112119 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21343_aux

theorem PEqualNP.Outside.L_meta_21343 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112119 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21343_aux.C, PEqualNP.Outside.L_meta_21343_aux.C_mono, PEqualNP.Outside.L_meta_21343_aux.C_size, PEqualNP.Outside.L_meta_21343_aux.C_rep⟩
