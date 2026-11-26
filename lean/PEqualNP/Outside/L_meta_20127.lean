import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20127_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 5]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [19, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [21, 17]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [22, 2]⟩, ⟨.or, [24, 8]⟩, ⟨.and, [26, 25]⟩, ⟨.or, [13, 0]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [9, 28]⟩, ⟨.or, [30, 1]⟩, ⟨.or, [14, 28]⟩, ⟨.or, [4, 31]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [34, 1]⟩, ⟨.or, [32, 23]⟩, ⟨.and, [36, 35]⟩, ⟨.or, [33, 24]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [35, 38]⟩, ⟨.and, [38, 39]⟩, ⟨.or, [37, 3]⟩, ⟨.or, [27, 41]⟩, ⟨.or, [43, 42]⟩, ⟨.and, [40, 44]⟩, ⟨.or, [29, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16816131623650294815 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20127_aux

theorem PEqualNP.Outside.L_meta_20127 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16816131623650294815 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20127_aux.main
