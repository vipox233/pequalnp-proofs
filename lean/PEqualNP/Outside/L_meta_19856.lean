import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19856_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 3]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [17, 7]⟩, ⟨.and, [15, 5]⟩, ⟨.or, [25, 18]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [14, 23]⟩, ⟨.or, [0, 32]⟩, ⟨.and, [32, 0]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [22, 35]⟩, ⟨.and, [29, 31]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [39, 33]⟩, ⟨.or, [24, 38]⟩, ⟨.or, [30, 28]⟩, ⟨.and, [41, 36]⟩, ⟨.or, [42, 34]⟩, ⟨.or, [40, 44]⟩, ⟨.or, [45, 43]⟩, ⟨.or, [37, 46]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8547244839380926170 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19856_aux

theorem PEqualNP.Outside.L_meta_19856 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8547244839380926170 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19856_aux.main
