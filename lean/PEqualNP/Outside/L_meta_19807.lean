import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19807_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 5]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [5, 15]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [0, 21]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [23, 4]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [11, 26]⟩, ⟨.and, [19, 26]⟩, ⟨.or, [12, 21]⟩, ⟨.or, [23, 29]⟩, ⟨.or, [17, 4]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [31, 18]⟩, ⟨.and, [17, 25]⟩, ⟨.or, [31, 30]⟩, ⟨.and, [33, 27]⟩, ⟨.and, [0, 30]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [35, 38]⟩, ⟨.and, [39, 22]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [34, 28]⟩, ⟨.or, [43, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10644482476643535765 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19807_aux

theorem PEqualNP.Outside.L_meta_19807 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10644482476643535765 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19807_aux.main
