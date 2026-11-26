import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20167_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 5]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [10, 22]⟩, ⟨.or, [23, 22]⟩, ⟨.and, [24, 26]⟩, ⟨.or, [6, 25]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [4, 21]⟩, ⟨.or, [29, 26]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [19, 28]⟩, ⟨.or, [33, 27]⟩, ⟨.or, [30, 23]⟩, ⟨.or, [0, 32]⟩, ⟨.or, [21, 18]⟩, ⟨.and, [18, 35]⟩, ⟨.and, [37, 20]⟩, ⟨.or, [39, 34]⟩, ⟨.or, [40, 38]⟩, ⟨.and, [31, 36]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20167_aux

theorem PEqualNP.Outside.L_meta_20167 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20167_aux.main
