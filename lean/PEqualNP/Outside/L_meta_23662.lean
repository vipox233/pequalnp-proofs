import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23662

def witnessFromL_meta_19387 : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [5, 1]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [17, 19]⟩], 20⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witnessFromL_meta_19387 := by
  have ok : witnessFromL_meta_19387.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_23662

open PEqualNP.Outside.L_meta_23662 in
theorem PEqualNP.Outside.L_meta_23662 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276286 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨witnessFromL_meta_19387, shape, by decide, by decide +kernel⟩
