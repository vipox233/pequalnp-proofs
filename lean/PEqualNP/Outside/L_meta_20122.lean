import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20122

-- a witness circuit found by a SAT search over the promise inputs (one vertex on each side)
def witness : Circuit :=
  ⟨[⟨.or, [8, 11]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [19, 9]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [16, 9]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [16, 10]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [30, 11]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

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

end PEqualNP.Outside.L_meta_20122

open PEqualNP.Outside.L_meta_20122 in
theorem PEqualNP.Outside.L_meta_20122 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7264353014310989955 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
