import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21962

def witness : Circuit :=
  ⟨[⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩

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

end PEqualNP.Outside.L_meta_21962

open PEqualNP.Outside.L_meta_21962 in
theorem PEqualNP.Outside.L_meta_21962 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33967 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
