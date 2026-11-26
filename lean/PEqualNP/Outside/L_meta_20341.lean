import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20341_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 13]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [22, 3]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [5, 26]⟩, ⟨.and, [27, 30]⟩, ⟨.or, [5, 17]⟩, ⟨.and, [31, 23]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [28, 33]⟩, ⟨.or, [34, 32]⟩, ⟨.and, [35, 21]⟩, ⟨.and, [36, 29]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [40, 37]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3120634772845828080 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20341_aux

theorem PEqualNP.Outside.L_meta_20341 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3120634772845828080 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20341_aux.main
