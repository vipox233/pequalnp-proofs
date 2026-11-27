import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22195_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.and, [1, 2]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.not, [1]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.not, [15]⟩
    ], 16⟩

theorem op_witness : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem eval_witness :
    ∀ i j : Fin 6,
      witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (17077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22195_aux

theorem PEqualNP.Outside.L_meta_22195 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22195_aux.witness,
   PEqualNP.Outside.L_meta_22195_aux.op_witness,
   by decide,
   PEqualNP.Outside.L_meta_22195_aux.eval_witness⟩
