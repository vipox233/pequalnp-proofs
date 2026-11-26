import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20148

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [10, 15]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [19, 13]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [24, 13]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [27, 16]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [21, 12]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [19, 14]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [21, 14]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [15, 20]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [40, 29]⟩, ⟨.or, [41, 31]⟩, ⟨.or, [42, 33]⟩, ⟨.or, [43, 35]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 39]⟩], 46⟩

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

end PEqualNP.Outside.L_meta_20148

open PEqualNP.Outside.L_meta_20148 in
theorem PEqualNP.Outside.L_meta_20148 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17315157982817101740 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
