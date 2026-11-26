import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19886_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 4]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [21, 3]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [20, 2]⟩, ⟨.or, [25, 28]⟩, ⟨.and, [29, 14]⟩, ⟨.or, [27, 0]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [21, 1]⟩, ⟨.or, [13, 23]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [10, 24]⟩, ⟨.or, [26, 25]⟩, ⟨.and, [34, 18]⟩, ⟨.or, [6, 38]⟩, ⟨.or, [17, 39]⟩, ⟨.and, [31, 40]⟩, ⟨.and, [37, 35]⟩, ⟨.and, [33, 32]⟩, ⟨.or, [30, 41]⟩, ⟨.or, [43, 44]⟩, ⟨.or, [36, 45]⟩, ⟨.or, [46, 42]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11335344517058034870 : ℕ).testBit (8 * u.val + v.val)) 37 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19886_aux

theorem PEqualNP.Outside.L_meta_19886 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11335344517058034870 : ℕ).testBit (8 * u.val + v.val)) 37 :=
  PEqualNP.Outside.L_meta_19886_aux.main
