import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22230

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [17, 9]⟩, ⟨.and, [13, 15]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [19, 20]⟩], 21⟩

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

end PEqualNP.Outside.L_meta_22230

open PEqualNP.Outside.L_meta_22230 in
theorem PEqualNP.Outside.L_meta_22230 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849916 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
