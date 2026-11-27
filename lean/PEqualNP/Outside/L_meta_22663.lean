import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22663

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [18, 13]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [22, 21]⟩], 23⟩

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

end PEqualNP.Outside.L_meta_22663

open PEqualNP.Outside.L_meta_22663 in
theorem PEqualNP.Outside.L_meta_22663 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841212 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
