import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20008_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 17]⟩, ⟨.and, [3, 18]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [10, 23]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [26, 14]⟩, ⟨.or, [1, 28]⟩, ⟨.or, [22, 4]⟩, ⟨.and, [20, 24]⟩, ⟨.or, [28, 23]⟩, ⟨.or, [14, 25]⟩, ⟨.and, [27, 33]⟩, ⟨.or, [29, 8]⟩, ⟨.and, [30, 35]⟩, ⟨.and, [19, 32]⟩, ⟨.or, [31, 37]⟩, ⟨.or, [36, 34]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [21, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2072365430907573360 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20008_aux

theorem PEqualNP.Outside.L_meta_20008 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2072365430907573360 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20008_aux.main
