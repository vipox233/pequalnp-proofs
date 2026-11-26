import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20022_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- 31 AND/OR gates of fan-in two (a rectangle cover with shared OR trees), found by a search. -/
def C_ : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [22, 7]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [28, 13]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [30, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [32, 15]⟩, ⟨.and, [18, 9]⟩, ⟨.and, [19, 26]⟩, ⟨.and, [24, 29]⟩, ⟨.and, [23, 14]⟩, ⟨.and, [17, 27]⟩, ⟨.and, [25, 33]⟩, ⟨.and, [20, 31]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 39]⟩, ⟨.or, [45, 40]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15289266858240601290 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20022_aux

theorem PEqualNP.Outside.L_meta_20022 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15289266858240601290 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20022_aux.main
