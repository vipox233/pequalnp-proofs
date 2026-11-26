import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20074_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 4]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [9, 22]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [16, 29]⟩, ⟨.and, [26, 22]⟩, ⟨.and, [23, 30]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [28, 10]⟩, ⟨.and, [27, 34]⟩, ⟨.or, [35, 32]⟩, ⟨.and, [20, 33]⟩, ⟨.or, [31, 37]⟩, ⟨.or, [38, 36]⟩, ⟨.or, [39, 25]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10108984885455782700 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20074_aux

theorem PEqualNP.Outside.L_meta_20074 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10108984885455782700 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20074_aux.main
