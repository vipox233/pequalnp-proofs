import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19907_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 12]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 20]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [23, 8]⟩, ⟨.or, [21, 25]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [21, 26]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [29, 32]⟩, ⟨.and, [34, 22]⟩, ⟨.and, [25, 32]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [10, 33]⟩, ⟨.and, [30, 24]⟩, ⟨.or, [26, 31]⟩, ⟨.or, [38, 3]⟩, ⟨.and, [40, 41]⟩, ⟨.or, [37, 42]⟩, ⟨.or, [39, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3937228359801398220 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19907_aux

theorem PEqualNP.Outside.L_meta_19907 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3937228359801398220 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19907_aux.main
