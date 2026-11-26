import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19897_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [17, 9]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [26, 14]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [25, 23]⟩, ⟨.and, [3, 27]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [19, 2]⟩, ⟨.or, [25, 22]⟩, ⟨.and, [20, 35]⟩, ⟨.and, [29, 28]⟩, ⟨.or, [11, 34]⟩, ⟨.and, [30, 38]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [40, 33]⟩, ⟨.or, [41, 39]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7226616402994737825 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19897_aux

theorem PEqualNP.Outside.L_meta_19897 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7226616402994737825 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_19897_aux.main
