import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19800_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [1, 23]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [26, 1]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [25, 29]⟩, ⟨.or, [23, 13]⟩, ⟨.or, [26, 21]⟩, ⟨.or, [17, 32]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [30, 18]⟩, ⟨.or, [24, 33]⟩, ⟨.or, [27, 7]⟩, ⟨.or, [33, 13]⟩, ⟨.or, [37, 11]⟩, ⟨.and, [38, 39]⟩, ⟨.or, [31, 7]⟩, ⟨.and, [41, 34]⟩, ⟨.or, [35, 42]⟩, ⟨.or, [18, 36]⟩, ⟨.or, [44, 25]⟩, ⟨.and, [22, 45]⟩, ⟨.or, [43, 46]⟩, ⟨.or, [40, 47]⟩], 48⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4317929078742808305 : ℕ).testBit (8 * u.val + v.val)) 37 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19800_aux

theorem PEqualNP.Outside.L_meta_19800 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4317929078742808305 : ℕ).testBit (8 * u.val + v.val)) 37 :=
  PEqualNP.Outside.L_meta_19800_aux.main
