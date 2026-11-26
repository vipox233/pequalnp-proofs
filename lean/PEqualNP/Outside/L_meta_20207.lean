import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20207_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 8]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [22, 2]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [19, 27]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [9, 29]⟩, ⟨.or, [21, 25]⟩, ⟨.and, [31, 24]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [20, 23]⟩, ⟨.and, [35, 30]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [25, 34]⟩, ⟨.or, [32, 37]⟩, ⟨.or, [37, 13]⟩, ⟨.or, [33, 36]⟩, ⟨.and, [28, 39]⟩, ⟨.and, [38, 40]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20207_aux

theorem PEqualNP.Outside.L_meta_20207 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20207_aux.main
