import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20134

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [9, 15]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [8, 19]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [18, 15]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [17, 12]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 19]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [6, 32]⟩, ⟨.or, [17, 10]⟩, ⟨.and, [7, 34]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [36, 25]⟩, ⟨.or, [37, 27]⟩, ⟨.or, [38, 29]⟩, ⟨.or, [39, 31]⟩, ⟨.or, [40, 33]⟩, ⟨.or, [41, 35]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_20134

open PEqualNP.Outside.L_meta_20134 in
theorem PEqualNP.Outside.L_meta_20134 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
