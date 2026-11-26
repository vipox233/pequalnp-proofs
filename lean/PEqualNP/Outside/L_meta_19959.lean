import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19959_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 6]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [28, 13]⟩, ⟨.or, [27, 9]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [29, 23]⟩, ⟨.or, [20, 9]⟩, ⟨.or, [32, 34]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [12, 28]⟩, ⟨.and, [26, 30]⟩, ⟨.and, [31, 36]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [4, 37]⟩, ⟨.and, [33, 40]⟩, ⟨.or, [38, 39]⟩, ⟨.and, [35, 41]⟩, ⟨.or, [44, 42]⟩, ⟨.or, [43, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19959_aux

theorem PEqualNP.Outside.L_meta_19959 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19959_aux.main
