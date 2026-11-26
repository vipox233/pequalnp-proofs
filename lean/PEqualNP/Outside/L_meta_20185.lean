import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20185_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 11]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [21, 15]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [14, 26]⟩, ⟨.or, [2, 23]⟩, ⟨.and, [28, 30]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [32, 27]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [22, 34]⟩, ⟨.or, [20, 26]⟩, ⟨.and, [33, 36]⟩, ⟨.or, [31, 35]⟩, ⟨.or, [38, 37]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20185_aux

theorem PEqualNP.Outside.L_meta_20185 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20185_aux.main
