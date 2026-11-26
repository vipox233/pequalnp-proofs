import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20070_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 11]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [17, 8]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [22, 3]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [14, 23]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [13, 23]⟩, ⟨.and, [24, 28]⟩, ⟨.or, [12, 27]⟩, ⟨.or, [25, 31]⟩, ⟨.and, [30, 26]⟩, ⟨.and, [5, 22]⟩, ⟨.or, [6, 33]⟩, ⟨.and, [16, 34]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [39, 36]⟩, ⟨.and, [29, 37]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 38]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15147095585269801245 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20070_aux

theorem PEqualNP.Outside.L_meta_20070 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15147095585269801245 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20070_aux.main
