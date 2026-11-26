import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19731_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 33 AND/OR gates: an OR of 7 rectangles (row-set OR AND column-set OR). -/
def C_ : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [17, 12]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [20, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [24, 25]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [27, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [29, 14]⟩, ⟨.and, [28, 30]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [32, 7]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [33, 35]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [37, 38]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [13, 15]⟩, ⟨.and, [40, 41]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [43, 26]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 36]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 42]⟩], 48⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19731_aux

theorem PEqualNP.Outside.L_meta_19731 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16914613873039728090 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19731_aux.main
