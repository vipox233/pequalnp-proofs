import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20309_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 14]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [9, 26]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [16, 24]⟩, ⟨.or, [27, 16]⟩, ⟨.or, [22, 33]⟩, ⟨.and, [31, 34]⟩, ⟨.and, [29, 25]⟩, ⟨.and, [22, 32]⟩, ⟨.or, [17, 26]⟩, ⟨.or, [36, 35]⟩, ⟨.and, [30, 23]⟩, ⟨.or, [21, 38]⟩, ⟨.and, [41, 28]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [37, 43]⟩, ⟨.or, [44, 39]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3115533915564101205 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20309_aux

theorem PEqualNP.Outside.L_meta_20309 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3115533915564101205 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20309_aux.main
