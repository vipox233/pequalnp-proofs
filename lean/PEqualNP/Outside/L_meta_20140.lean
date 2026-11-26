import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20140

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [21, 17]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [20, 10]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [19, 14]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [33, 15]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [13, 19]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [40, 27]⟩, ⟨.or, [41, 30]⟩, ⟨.or, [42, 32]⟩, ⟨.or, [43, 35]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_20140

open PEqualNP.Outside.L_meta_20140 in
theorem PEqualNP.Outside.L_meta_20140 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3306370337538841395 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
