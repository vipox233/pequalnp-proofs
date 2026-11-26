import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20219_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 11]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [21, 20]⟩, ⟨.and, [6, 21]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [27, 19]⟩, ⟨.or, [17, 28]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [22, 26]⟩, ⟨.or, [27, 18]⟩, ⟨.or, [29, 30]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [24, 33]⟩, ⟨.or, [9, 30]⟩, ⟨.or, [36, 16]⟩, ⟨.and, [37, 32]⟩, ⟨.or, [38, 31]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [35, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16256050495690680915 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20219_aux

theorem PEqualNP.Outside.L_meta_20219 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16256050495690680915 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20219_aux.main
