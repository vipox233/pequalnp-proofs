import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21387

def witness : Circuit :=
  ⟨[⟨.or, [3, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [12, 15]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

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

end PEqualNP.Outside.L_meta_21387

open PEqualNP.Outside.L_meta_21387 in
theorem PEqualNP.Outside.L_meta_21387 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106397 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
