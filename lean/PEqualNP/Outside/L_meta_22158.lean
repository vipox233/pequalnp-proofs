import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22158_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [4, 18]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [17, 19]⟩], 21⟩

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

theorem C_size : C.size ≤ 12 := by decide

theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840693 : ℕ).testBit (6 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_22158_aux

theorem PEqualNP.Outside.L_meta_22158 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840693 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22158_aux.C, PEqualNP.Outside.L_meta_22158_aux.C_mono, PEqualNP.Outside.L_meta_22158_aux.C_size, PEqualNP.Outside.L_meta_22158_aux.C_rep⟩
