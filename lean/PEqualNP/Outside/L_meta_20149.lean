import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20149

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [3, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [20, 0]⟩, ⟨.or, [22, 4]⟩, ⟨.and, [8, 23]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [9, 25]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [10, 27]⟩, ⟨.or, [17, 3]⟩, ⟨.or, [29, 18]⟩, ⟨.and, [11, 30]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [32, 0]⟩, ⟨.and, [12, 33]⟩, ⟨.or, [21, 16]⟩, ⟨.and, [13, 35]⟩, ⟨.or, [20, 5]⟩, ⟨.or, [37, 2]⟩, ⟨.and, [14, 38]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [40, 1]⟩, ⟨.and, [15, 41]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

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

end PEqualNP.Outside.L_meta_20149

open PEqualNP.Outside.L_meta_20149 in
theorem PEqualNP.Outside.L_meta_20149 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6759311759757734295 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
