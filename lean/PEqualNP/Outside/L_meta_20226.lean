import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20226_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 8]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [20, 7]⟩, ⟨.or, [24, 6]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [19, 21]⟩, ⟨.or, [9, 26]⟩, ⟨.or, [28, 22]⟩, ⟨.or, [24, 0]⟩, ⟨.or, [9, 22]⟩, ⟨.or, [23, 29]⟩, ⟨.or, [30, 10]⟩, ⟨.or, [1, 16]⟩, ⟨.and, [27, 35]⟩, ⟨.or, [33, 32]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [25, 31]⟩, ⟨.and, [40, 34]⟩, ⟨.and, [38, 39]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20226_aux

theorem PEqualNP.Outside.L_meta_20226 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20226_aux.main
