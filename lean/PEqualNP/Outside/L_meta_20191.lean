import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20191_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 1]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [19, 21]⟩, ⟨.and, [20, 17]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [3, 24]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [23, 21]⟩, ⟨.and, [25, 22]⟩, ⟨.or, [26, 19]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [16, 32]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [10, 22]⟩, ⟨.and, [30, 33]⟩, ⟨.and, [35, 31]⟩, ⟨.or, [27, 1]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [28, 38]⟩, ⟨.and, [40, 34]⟩, ⟨.or, [39, 41]⟩, ⟨.or, [29, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20191_aux

theorem PEqualNP.Outside.L_meta_20191 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20191_aux.main
