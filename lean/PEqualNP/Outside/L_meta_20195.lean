import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20195_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 12]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [8, 19]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [24, 8]⟩, ⟨.or, [7, 25]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [27, 18]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [26, 22]⟩, ⟨.and, [16, 32]⟩, ⟨.and, [15, 28]⟩, ⟨.and, [23, 29]⟩, ⟨.and, [30, 31]⟩, ⟨.or, [35, 33]⟩, ⟨.or, [34, 37]⟩, ⟨.or, [38, 36]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10678392892249613865 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20195_aux

theorem PEqualNP.Outside.L_meta_20195 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10678392892249613865 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20195_aux.main
