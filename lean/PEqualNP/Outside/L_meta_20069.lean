import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20069_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 10]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [23, 3]⟩, ⟨.and, [17, 24]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [15, 25]⟩, ⟨.or, [13, 21]⟩, ⟨.and, [22, 30]⟩, ⟨.or, [4, 28]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [26, 31]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [35, 34]⟩, ⟨.and, [33, 27]⟩, ⟨.and, [32, 16]⟩, ⟨.or, [29, 37]⟩, ⟨.or, [38, 36]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5899763987308416705 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20069_aux

theorem PEqualNP.Outside.L_meta_20069 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5899763987308416705 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20069_aux.main
