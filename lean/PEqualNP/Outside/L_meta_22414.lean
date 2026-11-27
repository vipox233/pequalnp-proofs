import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22414

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩

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

end PEqualNP.Outside.L_meta_22414

open PEqualNP.Outside.L_meta_22414 in
theorem PEqualNP.Outside.L_meta_22414 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (916476 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
