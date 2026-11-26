import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21174

def witness : Circuit := ⟨[⟨.or, [3, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [13, 17]⟩], 18⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have ok : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_21174

open PEqualNP.Outside.L_meta_21174 in
theorem PEqualNP.Outside.L_meta_21174 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103640 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
