import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19827_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [1, 21]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [2, 23]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [3, 25]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [4, 27]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [29, 14]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [32, 15]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [37, 24]⟩, ⟨.or, [38, 26]⟩, ⟨.or, [39, 28]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11710863513312518700 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19827_aux

theorem PEqualNP.Outside.L_meta_19827 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11710863513312518700 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19827_aux.main
