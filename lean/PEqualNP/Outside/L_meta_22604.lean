import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22604

def witnessFromL_meta_21371 : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [15, 0]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [19, 20]⟩, ⟨.or, [18, 21]⟩], 22⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witnessFromL_meta_21371 := by
  have ok : witnessFromL_meta_21371.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22604

open PEqualNP.Outside.L_meta_22604 in
theorem PEqualNP.Outside.L_meta_22604 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072252 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witnessFromL_meta_21371, shape, by decide, by decide +kernel⟩
