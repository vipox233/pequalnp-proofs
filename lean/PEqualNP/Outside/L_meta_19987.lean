import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19987_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 4]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [3, 18]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [12, 1]⟩, ⟨.and, [19, 20]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [14, 24]⟩, ⟨.or, [29, 22]⟩, ⟨.or, [23, 14]⟩, ⟨.or, [2, 27]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [4, 30]⟩, ⟨.or, [25, 33]⟩, ⟨.or, [26, 24]⟩, ⟨.or, [35, 10]⟩, ⟨.and, [34, 36]⟩, ⟨.and, [37, 31]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [17, 32]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [38, 43]⟩, ⟨.and, [42, 11]⟩, ⟨.or, [45, 41]⟩, ⟨.or, [46, 44]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19987_aux

theorem PEqualNP.Outside.L_meta_19987 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19987_aux.main
