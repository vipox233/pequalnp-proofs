import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24103_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [8, 13]⟩], 14⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_24103_aux

theorem PEqualNP.Outside.L_meta_24103 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4433 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24103_aux.witness, PEqualNP.Outside.L_meta_24103_aux.witnessFit, by decide, by decide +kernel⟩
