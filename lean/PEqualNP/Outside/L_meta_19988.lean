import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 4]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [19, 16]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [8, 21]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [8, 25]⟩, ⟨.or, [5, 27]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [26, 5]⟩, ⟨.or, [30, 24]⟩, ⟨.or, [31, 29]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [26, 22]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [33, 35]⟩, ⟨.and, [32, 34]⟩, ⟨.or, [36, 37]⟩, ⟨.and, [28, 20]⟩, ⟨.or, [39, 38]⟩, ⟨.or, [40, 23]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19988_aux

theorem PEqualNP.Outside.L_meta_19988 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_19988_aux.main
