import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19888_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [11, 1]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [17, 22]⟩, ⟨.and, [26, 23]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [27, 16]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [31, 25]⟩, ⟨.or, [30, 32]⟩, ⟨.or, [28, 12]⟩, ⟨.and, [33, 29]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [15, 31]⟩, ⟨.or, [33, 7]⟩, ⟨.or, [21, 36]⟩, ⟨.or, [37, 35]⟩, ⟨.and, [34, 39]⟩, ⟨.and, [40, 38]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14500150567228511850 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19888_aux

theorem PEqualNP.Outside.L_meta_19888 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14500150567228511850 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19888_aux.main
