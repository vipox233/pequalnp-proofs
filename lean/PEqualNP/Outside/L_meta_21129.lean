import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21129_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [8, 3]⟩
      , ⟨GateOp.or, [9, 5]⟩
      , ⟨GateOp.or, [0, 4]⟩
      , ⟨GateOp.or, [11, 5]⟩
      , ⟨GateOp.and, [10, 11]⟩
      , ⟨GateOp.or, [2, 7]⟩
      , ⟨GateOp.or, [14, 13]⟩
      , ⟨GateOp.or, [6, 15]⟩
      , ⟨GateOp.or, [12, 1]⟩
      , ⟨GateOp.and, [17, 16]⟩ ]
    output := 18 }

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (36254 : ℕ).testBit (5 * u.val + v.val)) circ := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_21129_aux

theorem PEqualNP.Outside.L_meta_21129 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36254 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_21129_aux.circ,
    PEqualNP.Outside.L_meta_21129_aux.mono,
    by decide,
    PEqualNP.Outside.L_meta_21129_aux.rep⟩
