import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20133_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [13, 2]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [17, 9]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [10, 10]⟩, ⟨.or, [22, 7]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [16, 24]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [26, 2]⟩, ⟨.or, [5, 20]⟩, ⟨.or, [23, 25]⟩, ⟨.and, [21, 23]⟩, ⟨.or, [15, 28]⟩, ⟨.or, [19, 31]⟩, ⟨.or, [27, 13]⟩, ⟨.or, [25, 18]⟩, ⟨.or, [32, 23]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [33, 31]⟩, ⟨.and, [29, 37]⟩, ⟨.or, [8, 30]⟩, ⟨.and, [36, 35]⟩, ⟨.or, [39, 6]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [33, 34]⟩, ⟨.and, [41, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16895921043476436375 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20133_aux

theorem PEqualNP.Outside.L_meta_20133 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16895921043476436375 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20133_aux.main
