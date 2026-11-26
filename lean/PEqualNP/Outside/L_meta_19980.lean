import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19980_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 12]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [17, 22]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [4, 26]⟩, ⟨.or, [20, 0]⟩, ⟨.and, [13, 29]⟩, ⟨.or, [23, 30]⟩, ⟨.and, [27, 24]⟩, ⟨.or, [19, 9]⟩, ⟨.or, [25, 10]⟩, ⟨.or, [17, 28]⟩, ⟨.and, [35, 34]⟩, ⟨.and, [32, 36]⟩, ⟨.or, [37, 33]⟩, ⟨.or, [31, 39]⟩, ⟨.or, [40, 38]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3033546467241018405 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19980_aux

theorem PEqualNP.Outside.L_meta_19980 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3033546467241018405 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19980_aux.main
