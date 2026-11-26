import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19901_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 11]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [10, 21]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [17, 8]⟩, ⟨.or, [9, 22]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [1, 24]⟩, ⟨.or, [11, 26]⟩, ⟨.and, [12, 19]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [25, 32]⟩, ⟨.or, [32, 9]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [29, 23]⟩, ⟨.or, [10, 29]⟩, ⟨.and, [28, 34]⟩, ⟨.and, [24, 31]⟩, ⟨.or, [27, 36]⟩, ⟨.and, [5, 37]⟩, ⟨.and, [35, 33]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [43, 41]⟩, ⟨.or, [44, 40]⟩, ⟨.or, [42, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15123525816772544370 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19901_aux

theorem PEqualNP.Outside.L_meta_19901 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15123525816772544370 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19901_aux.main
