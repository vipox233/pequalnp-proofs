import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20098

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [8, 24]⟩, ⟨.or, [20, 7]⟩, ⟨.or, [26, 16]⟩, ⟨.and, [9, 27]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [29, 22]⟩, ⟨.and, [10, 30]⟩, ⟨.or, [4, 23]⟩, ⟨.and, [11, 32]⟩, ⟨.or, [20, 22]⟩, ⟨.and, [12, 34]⟩, ⟨.or, [21, 5]⟩, ⟨.and, [13, 36]⟩, ⟨.or, [6, 21]⟩, ⟨.and, [14, 38]⟩, ⟨.or, [23, 2]⟩, ⟨.and, [15, 40]⟩, ⟨.or, [25, 28]⟩, ⟨.or, [42, 31]⟩, ⟨.or, [43, 33]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_20098

open PEqualNP.Outside.L_meta_20098 in
theorem PEqualNP.Outside.L_meta_20098 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
