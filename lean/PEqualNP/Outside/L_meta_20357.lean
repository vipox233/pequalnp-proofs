import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20357_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 4]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [25, 23]⟩, ⟨.or, [19, 26]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [24, 17]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [20, 28]⟩, ⟨.and, [27, 34]⟩, ⟨.and, [30, 29]⟩, ⟨.or, [32, 22]⟩, ⟨.or, [22, 18]⟩, ⟨.and, [33, 37]⟩, ⟨.and, [38, 31]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [36, 41]⟩, ⟨.or, [40, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15123525816772544370 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20357_aux

theorem PEqualNP.Outside.L_meta_20357 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15123525816772544370 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20357_aux.main
