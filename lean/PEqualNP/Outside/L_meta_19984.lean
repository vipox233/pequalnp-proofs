import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19984_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 13]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [18, 4]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [22, 8]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [23, 4]⟩, ⟨.or, [20, 3]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [23, 28]⟩, ⟨.or, [21, 19]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [20, 25]⟩, ⟨.and, [29, 26]⟩, ⟨.and, [34, 32]⟩, ⟨.and, [27, 30]⟩, ⟨.or, [35, 37]⟩, ⟨.and, [31, 24]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [36, 38]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1144228038332444715 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19984_aux

theorem PEqualNP.Outside.L_meta_19984 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1144228038332444715 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_19984_aux.main
