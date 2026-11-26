import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20071

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [23, 18]⟩, ⟨.and, [8, 24]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [9, 26]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [29, 2]⟩, ⟨.and, [10, 30]⟩, ⟨.or, [21, 22]⟩, ⟨.and, [11, 32]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [12, 34]⟩, ⟨.or, [22, 19]⟩, ⟨.and, [13, 36]⟩, ⟨.or, [19, 20]⟩, ⟨.and, [14, 38]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [40, 0]⟩, ⟨.and, [15, 41]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_20071

open PEqualNP.Outside.L_meta_20071 in
theorem PEqualNP.Outside.L_meta_20071 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8465338603409387505 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
