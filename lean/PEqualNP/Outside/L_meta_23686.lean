import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23686

def witnessFromL_meta_21057 : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [4, 18]⟩], 19⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witnessFromL_meta_21057 := by
  have ok : witnessFromL_meta_21057.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_23686

open PEqualNP.Outside.L_meta_23686 in
theorem PEqualNP.Outside.L_meta_23686 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816761 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨witnessFromL_meta_21057, shape, by decide, by decide +kernel⟩
