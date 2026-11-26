import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20222_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 12]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [19, 6]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [1, 20]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [27, 28]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [30, 9]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [33, 32]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [27, 31]⟩, ⟨.or, [6, 14]⟩, ⟨.and, [21, 26]⟩, ⟨.or, [38, 36]⟩, ⟨.and, [35, 29]⟩, ⟨.or, [34, 39]⟩, ⟨.and, [37, 40]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20222_aux

theorem PEqualNP.Outside.L_meta_20222 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20222_aux.main
