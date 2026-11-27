import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22440

def witnessFromL_meta_21373 : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [11, 0]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [16, 8]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [19, 3]⟩, ⟨.or, [20, 7]⟩, ⟨.and, [17, 21]⟩], 22⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witnessFromL_meta_21373 := by
  have ok : witnessFromL_meta_21373.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22440

open PEqualNP.Outside.L_meta_22440 in
theorem PEqualNP.Outside.L_meta_22440 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881903 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witnessFromL_meta_21373, shape, by decide, by decide +kernel⟩
