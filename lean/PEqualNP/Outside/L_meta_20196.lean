import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20196_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 3]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [23, 14]⟩, ⟨.or, [5, 20]⟩, ⟨.or, [19, 0]⟩, ⟨.or, [9, 23]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [29, 7]⟩, ⟨.or, [17, 11]⟩, ⟨.and, [21, 30]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [22, 33]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [5, 31]⟩, ⟨.or, [16, 26]⟩, ⟨.or, [33, 35]⟩, ⟨.and, [37, 38]⟩, ⟨.and, [34, 27]⟩, ⟨.or, [40, 39]⟩, ⟨.and, [28, 36]⟩, ⟨.or, [32, 41]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20196_aux

theorem PEqualNP.Outside.L_meta_20196 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20196_aux.main
