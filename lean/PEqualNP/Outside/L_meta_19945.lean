import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19945_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 13]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [18, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [15, 25]⟩, ⟨.or, [4, 24]⟩, ⟨.or, [23, 28]⟩, ⟨.and, [26, 6]⟩, ⟨.or, [30, 20]⟩, ⟨.and, [33, 31]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [35, 4]⟩, ⟨.and, [35, 29]⟩, ⟨.or, [18, 36]⟩, ⟨.or, [28, 38]⟩, ⟨.and, [39, 27]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [37, 19]⟩, ⟨.or, [32, 42]⟩, ⟨.or, [41, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15178139455177243725 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19945_aux

theorem PEqualNP.Outside.L_meta_19945 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15178139455177243725 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19945_aux.main
