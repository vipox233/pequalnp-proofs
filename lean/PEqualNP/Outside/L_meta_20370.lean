import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20370_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [19, 0]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [28, 25]⟩, ⟨.or, [27, 26]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [17, 28]⟩, ⟨.and, [29, 24]⟩, ⟨.or, [2, 22]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [3, 30]⟩, ⟨.and, [35, 21]⟩, ⟨.or, [36, 34]⟩, ⟨.and, [33, 37]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [39, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8398537473870936615 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20370_aux

theorem PEqualNP.Outside.L_meta_20370 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8398537473870936615 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20370_aux.main
