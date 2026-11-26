import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20386_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 5]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [20, 25]⟩, ⟨.or, [4, 27]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [2, 27]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [23, 26]⟩, ⟨.or, [32, 19]⟩, ⟨.or, [28, 22]⟩, ⟨.and, [31, 17]⟩, ⟨.or, [33, 36]⟩, ⟨.and, [35, 34]⟩, ⟨.or, [29, 3]⟩, ⟨.and, [30, 39]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20386_aux

theorem PEqualNP.Outside.L_meta_20386 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20386_aux.main
