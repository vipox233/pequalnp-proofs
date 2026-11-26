import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20277_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 2]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [5, 1]⟩, ⟨.and, [21, 24]⟩, ⟨.or, [3, 23]⟩, ⟨.and, [25, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [27, 9]⟩, ⟨.or, [16, 31]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [33, 8]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [35, 19]⟩, ⟨.or, [16, 29]⟩, ⟨.and, [36, 32]⟩, ⟨.and, [34, 37]⟩, ⟨.or, [39, 28]⟩, ⟨.or, [26, 40]⟩, ⟨.or, [38, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2278450633163008380 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20277_aux

theorem PEqualNP.Outside.L_meta_20277 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2278450633163008380 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20277_aux.main
