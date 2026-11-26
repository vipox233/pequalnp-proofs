import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20165_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 11]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [10, 21]⟩, ⟨.or, [22, 19]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [20, 8]⟩, ⟨.and, [7, 26]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [17, 8]⟩, ⟨.and, [25, 23]⟩, ⟨.and, [27, 29]⟩, ⟨.or, [10, 30]⟩, ⟨.or, [19, 20]⟩, ⟨.and, [18, 33]⟩, ⟨.or, [1, 16]⟩, ⟨.and, [36, 34]⟩, ⟨.or, [28, 35]⟩, ⟨.or, [38, 32]⟩, ⟨.or, [31, 39]⟩, ⟨.or, [40, 37]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20165_aux

theorem PEqualNP.Outside.L_meta_20165 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20165_aux.main
