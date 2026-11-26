import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19900_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 0]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [5, 25]⟩, ⟨.or, [22, 13]⟩, ⟨.and, [20, 28]⟩, ⟨.or, [15, 24]⟩, ⟨.and, [14, 27]⟩, ⟨.or, [10, 24]⟩, ⟨.and, [1, 23]⟩, ⟨.or, [6, 32]⟩, ⟨.or, [31, 33]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [26, 34]⟩, ⟨.or, [29, 35]⟩, ⟨.and, [37, 36]⟩, ⟨.and, [30, 17]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973835576939030640 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19900_aux

theorem PEqualNP.Outside.L_meta_19900 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973835576939030640 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19900_aux.main
