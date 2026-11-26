import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20060

def witness : Circuit :=
  ⟨[⟨.or, [0, 15]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [10, 27]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [30, 31]⟩, ⟨.and, [24, 28]⟩, ⟨.and, [17, 29]⟩, ⟨.and, [34, 32]⟩, ⟨.and, [33, 22]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [40, 38]⟩], 41⟩

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

end PEqualNP.Outside.L_meta_20060

open PEqualNP.Outside.L_meta_20060 in
theorem PEqualNP.Outside.L_meta_20060 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5918728716082980945 : ℕ).testBit (8 * u.val + v.val)) 26 := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
