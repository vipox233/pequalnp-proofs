import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19877_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 6]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [17, 3]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [20, 13]⟩, ⟨.and, [16, 15]⟩, ⟨.or, [23, 15]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [0, 22]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [27, 26]⟩, ⟨.or, [30, 0]⟩, ⟨.and, [29, 31]⟩, ⟨.and, [21, 2]⟩, ⟨.or, [3, 32]⟩, ⟨.and, [35, 25]⟩, ⟨.or, [22, 2]⟩, ⟨.or, [9, 26]⟩, ⟨.or, [24, 34]⟩, ⟨.and, [38, 37]⟩, ⟨.and, [30, 28]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [41, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6455152135695128040 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19877_aux

theorem PEqualNP.Outside.L_meta_19877 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6455152135695128040 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19877_aux.main
