import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20115_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [2, 21]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [9, 24]⟩, ⟨.and, [10, 21]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [30, 5]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [29, 15]⟩, ⟨.or, [23, 13]⟩, ⟨.and, [25, 32]⟩, ⟨.or, [33, 27]⟩, ⟨.and, [19, 34]⟩, ⟨.and, [28, 31]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [26, 39]⟩, ⟨.or, [36, 40]⟩, ⟨.or, [41, 37]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9687393527214586080 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20115_aux

theorem PEqualNP.Outside.L_meta_20115 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9687393527214586080 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20115_aux.main
