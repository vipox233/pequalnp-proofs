import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22418

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [16, 19]⟩], 20⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have ok : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22418

open PEqualNP.Outside.L_meta_22418 in
theorem PEqualNP.Outside.L_meta_22418 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1867386 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
