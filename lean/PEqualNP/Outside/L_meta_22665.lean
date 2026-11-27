import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22665

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [6, 8]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [16, 4]⟩, ⟨.and, [2, 17]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 19]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [21, 18]⟩, ⟨.or, [22, 20]⟩], 23⟩

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

end PEqualNP.Outside.L_meta_22665

open PEqualNP.Outside.L_meta_22665 in
theorem PEqualNP.Outside.L_meta_22665 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841526 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
