import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22647

def witness : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [3, 2]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [4, 15]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [5, 17]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [12, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [14, 22]⟩], 23⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have ok : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22647

open PEqualNP.Outside.L_meta_22647 in
theorem PEqualNP.Outside.L_meta_22647 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (819070 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
