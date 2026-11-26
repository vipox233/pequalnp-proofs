import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22518

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [2, 18]⟩, ⟨.and, [16, 19]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [12, 21]⟩], 22⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have ok : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22518

open PEqualNP.Outside.L_meta_22518 in
theorem PEqualNP.Outside.L_meta_22518 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900091 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
