import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22699

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [13, 9]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [15, 7]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [10, 14]⟩,
    ⟨.and, [11, 16]⟩,
    ⟨.and, [12, 17]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [20, 21]⟩], 22⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessMono : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_22699

open PEqualNP.Outside.L_meta_22699 in
theorem PEqualNP.Outside.L_meta_22699 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851261 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨witness, witnessMono, by decide, by decide +kernel⟩
