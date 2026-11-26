import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20692_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [5, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [15, 13]⟩, ⟨.or, [10, 16]⟩], 17⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15795200 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20692_aux

theorem PEqualNP.Outside.L_meta_20692 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15795200 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20692_aux.main
