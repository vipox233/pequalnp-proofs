import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20063

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [13, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [23, 11]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [8, 20]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [14, 20]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [30, 10]⟩, ⟨.or, [31, 13]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [18, 16]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [40, 27]⟩, ⟨.or, [41, 29]⟩, ⟨.or, [42, 33]⟩, ⟨.or, [43, 35]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_20063

open PEqualNP.Outside.L_meta_20063 in
theorem PEqualNP.Outside.L_meta_20063 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10768418131862349930 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
