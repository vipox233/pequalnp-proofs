import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19716

def witness : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [19, 15]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [1, 22]⟩,
    ⟨.or, [10, 18]⟩,
    ⟨.and, [2, 24]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.and, [3, 26]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [28, 15]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [7, 35]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [37, 25]⟩,
    ⟨.or, [38, 27]⟩,
    ⟨.or, [39, 30]⟩,
    ⟨.or, [40, 32]⟩,
    ⟨.or, [41, 34]⟩,
    ⟨.or, [42, 36]⟩], 43⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem shape : Monotone2 witness := by
  have allLegal : witness.gates.all legal = true := by decide +kernel
  intro g hg
  have ok := List.all_eq_true.mp allLegal g hg
  cases h : g.op <;> simp [legal, h] at ok ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_19716

open PEqualNP.Outside.L_meta_19716 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_19716 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9599430892109718240 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨witness, shape, by decide, by decide +kernel⟩
