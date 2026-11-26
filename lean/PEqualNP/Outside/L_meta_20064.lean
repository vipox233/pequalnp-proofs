import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20064_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 0]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [17, 7]⟩, ⟨.and, [20, 15]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [17, 23]⟩, ⟨.or, [6, 14]⟩, ⟨.and, [25, 18]⟩, ⟨.or, [17, 26]⟩, ⟨.or, [28, 24]⟩, ⟨.and, [20, 21]⟩, ⟨.or, [7, 24]⟩, ⟨.or, [31, 22]⟩, ⟨.and, [29, 19]⟩, ⟨.or, [32, 9]⟩, ⟨.or, [27, 33]⟩, ⟨.or, [0, 26]⟩, ⟨.or, [36, 15]⟩, ⟨.and, [34, 37]⟩, ⟨.or, [30, 38]⟩, ⟨.or, [35, 39]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16146478101879753735 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20064_aux

theorem PEqualNP.Outside.L_meta_20064 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16146478101879753735 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20064_aux.main
