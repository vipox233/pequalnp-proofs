import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20284_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 12]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [18, 9]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [7, 23]⟩, ⟨.or, [17, 24]⟩, ⟨.and, [25, 26]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [15, 22]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [9, 24]⟩, ⟨.and, [32, 20]⟩, ⟨.or, [31, 21]⟩, ⟨.and, [34, 28]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [33, 8]⟩, ⟨.or, [2, 37]⟩, ⟨.or, [27, 35]⟩, ⟨.or, [29, 36]⟩, ⟨.and, [38, 40]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6672462620410619475 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20284_aux

theorem PEqualNP.Outside.L_meta_20284 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6672462620410619475 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20284_aux.main
