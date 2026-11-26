import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21410

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [7, 16]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

def isMonoOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem isMonoOpSound (g : Gate) (ok : isMonoOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [isMonoOp, h] at ok ⊢

theorem witnessMono : Monotone2 witness := by
  have legal : witness.gates.all (fun g => isMonoOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨isMonoOpSound g passed.1, passed.2⟩

theorem witnessSize : witness.size ≤ 12 := by
  decide

theorem witnessRep :
    PEqualNP.Represents.Represents
      (fun (u : Fin 4) (v : Fin 5) => (241405 : ℕ).testBit (5 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_21410

theorem PEqualNP.Outside.L_meta_21410 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241405 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_21410.witness, PEqualNP.Outside.L_meta_21410.witnessMono, PEqualNP.Outside.L_meta_21410.witnessSize, PEqualNP.Outside.L_meta_21410.witnessRep⟩
