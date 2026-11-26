import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20310_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 12]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [19, 8]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [19, 10]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [24, 25]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [31, 23]⟩, ⟨.and, [33, 30]⟩, ⟨.or, [34, 32]⟩, ⟨.or, [26, 29]⟩, ⟨.or, [8, 27]⟩, ⟨.and, [5, 26]⟩, ⟨.or, [39, 38]⟩, ⟨.and, [22, 31]⟩, ⟨.and, [36, 28]⟩, ⟨.or, [40, 41]⟩, ⟨.and, [43, 37]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 42]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13418315418863193045 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20310_aux

theorem PEqualNP.Outside.L_meta_20310 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13418315418863193045 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20310_aux.main
