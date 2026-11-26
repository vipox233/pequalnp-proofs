import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20227_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 1]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [20, 22]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [28, 29]⟩, ⟨.and, [9, 26]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [30, 31]⟩, ⟨.and, [26, 11]⟩, ⟨.or, [33, 37]⟩, ⟨.or, [36, 38]⟩, ⟨.or, [25, 34]⟩, ⟨.and, [35, 40]⟩, ⟨.or, [39, 27]⟩, ⟨.or, [32, 41]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15221827736417774580 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20227_aux

theorem PEqualNP.Outside.L_meta_20227 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15221827736417774580 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20227_aux.main
