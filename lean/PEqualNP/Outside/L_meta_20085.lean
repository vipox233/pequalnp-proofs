import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20085

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [3, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [5, 21]⟩, ⟨.and, [8, 22]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [9, 24]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [26, 18]⟩, ⟨.and, [10, 27]⟩, ⟨.or, [21, 7]⟩, ⟨.and, [11, 29]⟩, ⟨.or, [18, 16]⟩, ⟨.and, [12, 31]⟩, ⟨.or, [19, 16]⟩, ⟨.and, [13, 33]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [35, 6]⟩, ⟨.and, [14, 36]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [15, 38]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [40, 28]⟩, ⟨.or, [41, 30]⟩, ⟨.or, [42, 32]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_20085

open PEqualNP.Outside.L_meta_20085 in
theorem PEqualNP.Outside.L_meta_20085 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6650604754610151990 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
