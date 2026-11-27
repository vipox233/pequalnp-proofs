import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22504

def witness : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [17, 8]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [21, 4]⟩], 22⟩

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

end PEqualNP.Outside.L_meta_22504

open PEqualNP.Outside.L_meta_22504 in
theorem PEqualNP.Outside.L_meta_22504 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898107 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
