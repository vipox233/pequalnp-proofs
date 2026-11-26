import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20247_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 6]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [4, 20]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [16, 5]⟩, ⟨.and, [16, 22]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [27, 21]⟩, ⟨.or, [26, 17]⟩, ⟨.or, [1, 28]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [10, 23]⟩, ⟨.and, [14, 0]⟩, ⟨.or, [33, 26]⟩, ⟨.or, [13, 21]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [34, 5]⟩, ⟨.and, [29, 32]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [40, 31]⟩, ⟨.and, [30, 41]⟩, ⟨.or, [39, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20247_aux

theorem PEqualNP.Outside.L_meta_20247 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20247_aux.main
