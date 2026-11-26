import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20131

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [2, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [16, 3]⟩, ⟨.and, [8, 20]⟩, ⟨.or, [2, 19]⟩, ⟨.and, [9, 22]⟩, ⟨.or, [17, 1]⟩, ⟨.and, [10, 24]⟩, ⟨.or, [18, 7]⟩, ⟨.and, [11, 26]⟩, ⟨.or, [17, 5]⟩, ⟨.and, [12, 28]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [13, 30]⟩, ⟨.or, [19, 6]⟩, ⟨.and, [14, 32]⟩, ⟨.or, [4, 18]⟩, ⟨.and, [15, 34]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [36, 25]⟩, ⟨.or, [37, 27]⟩, ⟨.or, [38, 29]⟩, ⟨.or, [39, 31]⟩, ⟨.or, [40, 33]⟩, ⟨.or, [41, 35]⟩], 42⟩

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

end PEqualNP.Outside.L_meta_20131

open PEqualNP.Outside.L_meta_20131 in
theorem PEqualNP.Outside.L_meta_20131 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2045083468351882920 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
