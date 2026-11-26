import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19985_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 2]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [15, 22]⟩, ⟨.and, [19, 20]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [25, 26]⟩, ⟨.or, [4, 28]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [31, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [32, 23]⟩, ⟨.and, [27, 29]⟩, ⟨.or, [21, 17]⟩, ⟨.and, [28, 36]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [38, 37]⟩, ⟨.and, [33, 18]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19985_aux

theorem PEqualNP.Outside.L_meta_19985 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19985_aux.main
