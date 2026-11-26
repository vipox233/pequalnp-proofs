import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19839_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [16, 21]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [23, 24]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [0, 26]⟩, ⟨.or, [11, 27]⟩, ⟨.or, [12, 28]⟩, ⟨.or, [17, 29]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [28, 31]⟩, ⟨.or, [5, 32]⟩, ⟨.or, [9, 33]⟩, ⟨.and, [30, 34]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [24, 37]⟩, ⟨.and, [36, 38]⟩, ⟨.and, [4, 23]⟩, ⟨.or, [12, 38]⟩, ⟨.and, [6, 41]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [39, 43]⟩, ⟨.or, [35, 44]⟩], 45⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19839_aux

theorem PEqualNP.Outside.L_meta_19839 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12762594853557972675 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_19839_aux.witness, PEqualNP.Outside.L_meta_19839_aux.witnessFit, by decide, by decide +kernel⟩
