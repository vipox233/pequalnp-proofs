import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_25374

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [11, 12]⟩], 13⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessMono : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_25374

open PEqualNP.Outside.L_meta_25374 in
theorem PEqualNP.Outside.L_meta_25374 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4378299 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, witnessMono, by decide, by decide +kernel⟩
