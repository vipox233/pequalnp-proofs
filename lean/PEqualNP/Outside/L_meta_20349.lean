import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20349_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 11]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [14, 24]⟩, ⟨.or, [23, 12]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [30, 15]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [24, 31]⟩, ⟨.or, [25, 19]⟩, ⟨.and, [34, 29]⟩, ⟨.and, [22, 27]⟩, ⟨.and, [26, 32]⟩, ⟨.and, [33, 28]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [36, 39]⟩, ⟨.or, [40, 37]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 26 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20349_aux

theorem PEqualNP.Outside.L_meta_20349 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 26 :=
  PEqualNP.Outside.L_meta_20349_aux.main
