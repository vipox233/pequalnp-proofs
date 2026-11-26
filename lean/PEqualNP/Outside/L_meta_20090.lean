import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20090_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 3]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [23, 10]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [21, 4]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [9, 23]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [5, 22]⟩, ⟨.or, [26, 6]⟩, ⟨.or, [22, 31]⟩, ⟨.and, [34, 35]⟩, ⟨.or, [16, 29]⟩, ⟨.or, [17, 30]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [5, 24]⟩, ⟨.and, [38, 33]⟩, ⟨.and, [40, 27]⟩, ⟨.or, [43, 42]⟩, ⟨.and, [32, 41]⟩, ⟨.or, [44, 45]⟩, ⟨.or, [46, 36]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13595087219314816350 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20090_aux

theorem PEqualNP.Outside.L_meta_20090 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13595087219314816350 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20090_aux.main
