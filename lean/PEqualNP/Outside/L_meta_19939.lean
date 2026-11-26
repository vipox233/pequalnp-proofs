import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19939_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 0]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [15, 2]⟩, ⟨.and, [16, 13]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [6, 24]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [29, 8]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [17, 2]⟩, ⟨.and, [33, 27]⟩, ⟨.and, [30, 37]⟩, ⟨.and, [34, 36]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 23]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19939_aux

theorem PEqualNP.Outside.L_meta_19939 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19939_aux.main
