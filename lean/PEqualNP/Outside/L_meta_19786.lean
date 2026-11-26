import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19786

def witness : Circuit :=
  ⟨[⟨.or, [8, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [20, 16]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [23, 18]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [26, 17]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [39, 17]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [42, 28]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 41]⟩], 48⟩

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

end PEqualNP.Outside.L_meta_19786

open PEqualNP.Outside.L_meta_19786 in
theorem PEqualNP.Outside.L_meta_19786 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770687136455741005 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
