import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25957

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [11, 12]⟩], 13⟩

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

end PEqualNP.Outside.L_meta_25957

theorem PEqualNP.Outside.L_meta_25957 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 3, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_25957.witness, PEqualNP.Outside.L_meta_25957.witnessFit, by decide, by decide,
    by decide +kernel⟩
