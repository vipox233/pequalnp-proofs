import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20048

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [8, 22]⟩, ⟨.or, [3, 19]⟩, ⟨.and, [9, 24]⟩, ⟨.or, [2, 20]⟩, ⟨.and, [10, 26]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [28, 5]⟩, ⟨.and, [11, 29]⟩, ⟨.or, [5, 21]⟩, ⟨.and, [12, 31]⟩, ⟨.or, [20, 0]⟩, ⟨.and, [13, 33]⟩, ⟨.or, [7, 19]⟩, ⟨.and, [14, 35]⟩, ⟨.or, [21, 6]⟩, ⟨.and, [15, 37]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [39, 27]⟩, ⟨.or, [40, 30]⟩, ⟨.or, [41, 32]⟩, ⟨.or, [42, 34]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 38]⟩], 45⟩

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

end PEqualNP.Outside.L_meta_20048

open PEqualNP.Outside.L_meta_20048 in
theorem PEqualNP.Outside.L_meta_20048 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15116961972522724785 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
