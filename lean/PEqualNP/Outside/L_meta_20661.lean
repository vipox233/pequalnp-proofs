import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20661_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [14, 12]⟩, ⟨.and, [13, 15]⟩], 16⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14877696 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20661_aux

theorem PEqualNP.Outside.L_meta_20661 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14877696 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20661_aux.main
