import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20371_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [19, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [24, 3]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [20, 27]⟩, ⟨.or, [26, 23]⟩, ⟨.and, [29, 16]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [28, 30]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [1, 25]⟩, ⟨.or, [33, 23]⟩, ⟨.and, [35, 31]⟩, ⟨.and, [22, 34]⟩, ⟨.or, [36, 32]⟩, ⟨.or, [38, 37]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1028405700185973360 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20371_aux

theorem PEqualNP.Outside.L_meta_20371 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1028405700185973360 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20371_aux.main
