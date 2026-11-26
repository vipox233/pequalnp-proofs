import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20350_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 8]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [18, 12]⟩, ⟨.or, [20, 1]⟩, ⟨.or, [2, 25]⟩, ⟨.and, [13, 21]⟩, ⟨.or, [21, 13]⟩, ⟨.and, [21, 17]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [24, 23]⟩, ⟨.or, [19, 29]⟩, ⟨.or, [33, 2]⟩, ⟨.and, [31, 27]⟩, ⟨.or, [35, 32]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [30, 36]⟩, ⟨.and, [37, 34]⟩, ⟨.or, [39, 38]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7264353014310989955 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20350_aux

theorem PEqualNP.Outside.L_meta_20350 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7264353014310989955 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  PEqualNP.Outside.L_meta_20350_aux.main
