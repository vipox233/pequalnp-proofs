import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19996_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 13]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [20, 3]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [11, 25]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [29, 11]⟩, ⟨.or, [30, 3]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [26, 31]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [0, 32]⟩, ⟨.and, [22, 33]⟩, ⟨.and, [27, 35]⟩, ⟨.and, [21, 34]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [4, 30]⟩, ⟨.or, [23, 28]⟩, ⟨.or, [40, 17]⟩, ⟨.and, [41, 42]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 39]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19996_aux

theorem PEqualNP.Outside.L_meta_19996 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19996_aux.main
