import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22540

def witness : Circuit :=
  ⟨[⟨.or, [7, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [12, 9]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [17, 0]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [20, 21]⟩], 22⟩

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

end PEqualNP.Outside.L_meta_22540

open PEqualNP.Outside.L_meta_22540 in
theorem PEqualNP.Outside.L_meta_22540 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939435 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
