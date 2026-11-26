import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20073_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 4]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [17, 3]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [15, 2]⟩, ⟨.and, [3, 3]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [2, 26]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [29, 21]⟩, ⟨.or, [26, 12]⟩, ⟨.or, [31, 29]⟩, ⟨.or, [28, 12]⟩, ⟨.or, [13, 34]⟩, ⟨.or, [1, 36]⟩, ⟨.or, [30, 31]⟩, ⟨.or, [27, 10]⟩, ⟨.and, [35, 38]⟩, ⟨.or, [33, 25]⟩, ⟨.or, [24, 39]⟩, ⟨.and, [32, 42]⟩, ⟨.or, [43, 40]⟩, ⟨.and, [37, 41]⟩, ⟨.or, [23, 44]⟩, ⟨.or, [46, 45]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8572844398234278885 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20073_aux

theorem PEqualNP.Outside.L_meta_20073 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8572844398234278885 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20073_aux.main
