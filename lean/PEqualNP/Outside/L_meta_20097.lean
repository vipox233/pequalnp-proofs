import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20097_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 3]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [4, 16]⟩, ⟨.and, [21, 8]⟩, ⟨.and, [19, 5]⟩, ⟨.or, [20, 2]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [28, 27]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [16, 26]⟩, ⟨.and, [9, 29]⟩, ⟨.or, [18, 12]⟩, ⟨.and, [30, 27]⟩, ⟨.or, [25, 1]⟩, ⟨.or, [24, 34]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [22, 33]⟩, ⟨.or, [31, 14]⟩, ⟨.or, [37, 13]⟩, ⟨.and, [40, 38]⟩, ⟨.or, [32, 36]⟩, ⟨.and, [35, 39]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2220931727598570300 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20097_aux

theorem PEqualNP.Outside.L_meta_20097 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2220931727598570300 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20097_aux.main
