import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19747

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [11, 20]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [8, 21]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [13, 20]⟩,
    ⟨.and, [2, 26]⟩,
    ⟨.or, [15, 21]⟩,
    ⟨.and, [3, 28]⟩,
    ⟨.or, [9, 21]⟩,
    ⟨.and, [4, 30]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.or, [32, 19]⟩,
    ⟨.and, [5, 33]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [35, 18]⟩,
    ⟨.and, [6, 36]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.and, [7, 38]⟩,
    ⟨.or, [23, 25]⟩,
    ⟨.or, [40, 27]⟩,
    ⟨.or, [41, 29]⟩,
    ⟨.or, [42, 31]⟩,
    ⟨.or, [43, 34]⟩,
    ⟨.or, [44, 37]⟩,
    ⟨.or, [45, 39]⟩], 46⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have allLegal : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have ok := List.all_eq_true.mp allLegal g hg
  cases h : g.op <;> simp [legal, h] at ok ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_19747

open PEqualNP.Outside.L_meta_19747 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_19747 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14348455746820602255 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
