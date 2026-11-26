import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19748_aux

def witness : Circuit :=
  ⟨[⟨.or, [11, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [19, 0]⟩, ⟨.or, [8, 22]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [23, 14]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [28, 11]⟩, ⟨.or, [19, 27]⟩, ⟨.and, [9, 20]⟩, ⟨.and, [24, 30]⟩, ⟨.or, [32, 2]⟩, ⟨.and, [16, 34]⟩, ⟨.and, [29, 21]⟩, ⟨.and, [22, 18]⟩, ⟨.or, [33, 36]⟩, ⟨.or, [35, 37]⟩, ⟨.and, [31, 26]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [41, 40]⟩], 42⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_19748_aux

open PEqualNP.Outside.L_meta_19748_aux in
theorem PEqualNP.Outside.L_meta_19748 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8124800356567354635 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  first
  | exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
  | exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩
  | (unfold PEqualNP.Represents.RepSizeAtMost; exact ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩)
