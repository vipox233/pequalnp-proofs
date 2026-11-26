import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20139_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [21, 16]⟩, ⟨.or, [15, 1]⟩, ⟨.and, [21, 23]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [20, 27]⟩, ⟨.or, [28, 23]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [22, 29]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [31, 33]⟩, ⟨.or, [30, 17]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [34, 0]⟩, ⟨.and, [35, 26]⟩, ⟨.and, [36, 37]⟩, ⟨.or, [32, 38]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3751079755257373080 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20139_aux

theorem PEqualNP.Outside.L_meta_20139 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3751079755257373080 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20139_aux.main
