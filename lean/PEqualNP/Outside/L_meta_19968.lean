import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19968_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 1]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [28, 24]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [17, 27]⟩, ⟨.or, [28, 19]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [30, 22]⟩, ⟨.and, [18, 33]⟩, ⟨.and, [26, 32]⟩, ⟨.or, [35, 0]⟩, ⟨.or, [34, 36]⟩, ⟨.or, [33, 2]⟩, ⟨.or, [5, 39]⟩, ⟨.or, [40, 25]⟩, ⟨.or, [29, 37]⟩, ⟨.or, [31, 2]⟩, ⟨.and, [41, 42]⟩, ⟨.and, [43, 23]⟩, ⟨.or, [45, 44]⟩, ⟨.or, [38, 46]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19968_aux

theorem PEqualNP.Outside.L_meta_19968 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15272338331126939085 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19968_aux.main
