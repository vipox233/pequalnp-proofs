import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 13]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [21, 2]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [20, 1]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [24, 23]⟩, ⟨.or, [25, 11]⟩, ⟨.and, [24, 27]⟩, ⟨.or, [25, 3]⟩, ⟨.and, [30, 28]⟩, ⟨.and, [32, 31]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [35, 33]⟩, ⟨.and, [37, 34]⟩, ⟨.or, [38, 36]⟩, ⟨.or, [40, 17]⟩, ⟨.and, [29, 27]⟩, ⟨.or, [41, 39]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19904_aux

theorem PEqualNP.Outside.L_meta_19904 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19904_aux.main
