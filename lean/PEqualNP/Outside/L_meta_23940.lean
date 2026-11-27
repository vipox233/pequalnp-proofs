import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23940

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩

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

end PEqualNP.Outside.L_meta_23940

open PEqualNP.Outside.L_meta_23940 in
theorem PEqualNP.Outside.L_meta_23940 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4501 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
