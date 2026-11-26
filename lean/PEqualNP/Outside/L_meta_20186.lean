import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20186_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 9]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [17, 9]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [22, 19]⟩, ⟨.or, [25, 22]⟩, ⟨.and, [25, 22]⟩, ⟨.or, [6, 27]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [11, 26]⟩, ⟨.and, [18, 30]⟩, ⟨.or, [23, 30]⟩, ⟨.or, [0, 29]⟩, ⟨.and, [33, 24]⟩, ⟨.or, [12, 28]⟩, ⟨.or, [36, 5]⟩, ⟨.and, [31, 21]⟩, ⟨.or, [35, 32]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [37, 40]⟩, ⟨.or, [41, 39]⟩, ⟨.or, [38, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20186_aux

theorem PEqualNP.Outside.L_meta_20186 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20186_aux.main
